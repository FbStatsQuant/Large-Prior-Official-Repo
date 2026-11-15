required_packages <- c("ggplot2", "horseshoe")

check_ridge_hs_packages <- function() {
  missing <- required_packages[
    !vapply(required_packages, requireNamespace, logical(1), quietly = TRUE)
  ]

  if (length(missing) > 0L) {
    stop(
      "Missing required R packages: ",
      paste(missing, collapse = ", "),
      ". Install them before running the simulation.",
      call. = FALSE
    )
  }
}

parse_ridge_hs_args <- function(args = commandArgs(trailingOnly = TRUE)) {
  options <- list(
    quick = FALSE,
    n = 1000L,
    fit_J = 125L,
    J_grid = seq.int(140L, 300L, by = 20L),
    burn = 1000L,
    nmc = 5000L,
    thin = 1L,
    nfolds = 20L,
    skip_grid = FALSE,
    output_root = NULL
  )

  for (arg in args) {
    if (identical(arg, "--quick")) {
      options$quick <- TRUE
    } else if (identical(arg, "--skip-grid")) {
      options$skip_grid <- TRUE
    } else if (grepl("^--n=", arg)) {
      options$n <- as.integer(sub("^--n=", "", arg))
    } else if (grepl("^--fit-J=", arg)) {
      options$fit_J <- as.integer(sub("^--fit-J=", "", arg))
    } else if (grepl("^--J-grid=", arg)) {
      raw_grid <- sub("^--J-grid=", "", arg)
      options$J_grid <- as.integer(strsplit(raw_grid, ",", fixed = TRUE)[[1L]])
    } else if (grepl("^--burn=", arg)) {
      options$burn <- as.integer(sub("^--burn=", "", arg))
    } else if (grepl("^--nmc=", arg)) {
      options$nmc <- as.integer(sub("^--nmc=", "", arg))
    } else if (grepl("^--thin=", arg)) {
      options$thin <- as.integer(sub("^--thin=", "", arg))
    } else if (grepl("^--nfolds=", arg)) {
      options$nfolds <- as.integer(sub("^--nfolds=", "", arg))
    } else if (grepl("^--output-root=", arg)) {
      options$output_root <- sub("^--output-root=", "", arg)
    } else {
      stop("Unknown argument: ", arg, call. = FALSE)
    }
  }

  if (isTRUE(options$quick)) {
    options$fit_J <- 60L
    options$J_grid <- c(40L, 60L, 80L)
    options$burn <- 100L
    options$nmc <- 200L
  }

  integer_fields <- c("n", "fit_J", "burn", "nmc", "thin", "nfolds")
  for (field in integer_fields) {
    value <- options[[field]]
    if (length(value) != 1L || is.na(value) || value < 1L) {
      stop("--", field, " must be a positive integer.", call. = FALSE)
    }
  }

  if (anyNA(options$J_grid) || any(options$J_grid < 2L)) {
    stop("--J-grid must contain comma-separated integers of at least 2.", call. = FALSE)
  }

  options$J_grid <- sort(unique(options$J_grid))
  options
}

# Build a real periodic Fourier dictionary with exactly J columns.
# Column 1 is the constant. Subsequent columns are complete sine/cosine pairs;
# when J is even, the final unpaired column is the next cosine term.
fourier_dictionary <- function(x, J) {
  stopifnot(J >= 2L)

  basis <- matrix(1, nrow = length(x), ncol = J)
  column_names <- character(J)
  column_names[1L] <- "constant"

  complete_pairs <- (J - 1L) %/% 2L
  next_column <- 2L

  if (complete_pairs > 0L) {
    for (k in seq_len(complete_pairs)) {
      basis[, next_column] <- sin(2 * pi * k * x)
      column_names[next_column] <- paste0("sin_", k)
      next_column <- next_column + 1L

      basis[, next_column] <- cos(2 * pi * k * x)
      column_names[next_column] <- paste0("cos_", k)
      next_column <- next_column + 1L
    }
  }

  if (next_column <= J) {
    k <- complete_pairs + 1L
    basis[, next_column] <- cos(2 * pi * k * x)
    column_names[next_column] <- paste0("cos_", k)
  }

  colnames(basis) <- column_names
  basis
}

make_cv_folds <- function(n, nfolds, seed) {
  if (nfolds > n) {
    stop("The number of CV folds cannot exceed n.", call. = FALSE)
  }

  set.seed(seed)
  sample(rep(seq_len(nfolds), length.out = n))
}

fit_horseshoe_fourier <- function(y, design, sigma, burn, nmc, thin, seed) {
  set.seed(seed)
  fit <- horseshoe::horseshoe(
    y = y,
    X = design,
    method.tau = "halfCauchy",
    method.sigma = "fixed",
    Sigma2 = sigma^2,
    burn = burn,
    nmc = nmc,
    thin = thin
  )

  coefficients <- drop(fit$BetaHat)
  list(
    fitted = drop(design %*% coefficients),
    coefficients = coefficients,
    tau_posterior_mean = unname(fit$TauHat)
  )
}

fit_ridge_fourier <- function(y, design, foldid, nfolds) {
  # Cross-validate the exact objective printed in the paper:
  #   ||y - X beta||^2 + lambda * ||beta||^2.
  # A direct eigendecomposition is used because glmnet treats a constant
  # dictionary column as a zero-variance predictor and drops it when
  # intercept=FALSE. The direct solution penalizes every Fourier coefficient,
  # including the constant, exactly as the displayed objective states.
  design_scale <- max(diag(crossprod(design)))
  lambda_rss_grid <- design_scale * 10^seq(4, -8, length.out = 160L)
  cv_sse <- numeric(length(lambda_rss_grid))

  for (fold in seq_len(nfolds)) {
    test_index <- foldid == fold
    train_design <- design[!test_index, , drop = FALSE]
    test_design <- design[test_index, , drop = FALSE]
    train_y <- y[!test_index]
    test_y <- y[test_index]

    decomposition <- eigen(
      crossprod(train_design),
      symmetric = TRUE
    )
    rotated_score <- drop(
      crossprod(
        decomposition$vectors,
        crossprod(train_design, train_y)
      )
    )
    denominator <- outer(
      decomposition$values,
      lambda_rss_grid,
      "+"
    )
    rotated_path <- matrix(
      rotated_score,
      nrow = length(rotated_score),
      ncol = length(lambda_rss_grid)
    ) / denominator
    coefficient_path <- decomposition$vectors %*% rotated_path
    prediction_path <- test_design %*% coefficient_path
    residual_path <- sweep(prediction_path, 1L, test_y, FUN = "-")
    cv_sse <- cv_sse + colSums(residual_path^2)
  }

  selected_index <- which.min(cv_sse)
  lambda_rss <- lambda_rss_grid[selected_index]

  full_decomposition <- eigen(crossprod(design), symmetric = TRUE)
  full_rotated_score <- drop(
    crossprod(
      full_decomposition$vectors,
      crossprod(design, y)
    )
  )
  coefficients <- drop(
    full_decomposition$vectors %*%
      (full_rotated_score / (full_decomposition$values + lambda_rss))
  )

  list(
    fitted = drop(design %*% coefficients),
    coefficients = coefficients,
    lambda_rss = lambda_rss,
    # Equivalent coefficient for MSE + lambda*||beta||^2.
    lambda_per_observation = lambda_rss / nrow(design),
    cv_mse = cv_sse[selected_index] / length(y)
  )
}

base_plot_theme <- function() {
  ggplot2::theme_minimal(base_size = 11) +
    ggplot2::theme(
      panel.grid.minor = ggplot2::element_blank(),
      plot.title = ggplot2::element_text(face = "bold"),
      legend.position = "bottom",
      legend.title = ggplot2::element_blank()
    )
}

save_fit_plot <- function(plot_data, config, options, output_dir) {
  method_data <- rbind(
    data.frame(
      x = plot_data$x,
      estimate = plot_data$horseshoe,
      method = "Horseshoe"
    ),
    data.frame(
      x = plot_data$x,
      estimate = plot_data$ridge,
      method = "Ridge"
    )
  )
  method_data$method <- factor(
    method_data$method,
    levels = c("Horseshoe", "Ridge")
  )

  fit_plot <- ggplot2::ggplot(
    method_data,
    ggplot2::aes(x = x, y = estimate, color = method, linetype = method)
  ) +
    ggplot2::geom_line(linewidth = 0.65) +
    ggplot2::geom_line(
      data = plot_data,
      ggplot2::aes(x = x, y = truth),
      inherit.aes = FALSE,
      color = "#1A1A1A",
      linewidth = 0.9
    ) +
    ggplot2::scale_color_manual(
      values = c(Horseshoe = "#2457A6", Ridge = "#D17A22")
    ) +
    ggplot2::scale_linetype_manual(
      values = c(Horseshoe = "solid", Ridge = "22")
    ) +
    ggplot2::labs(
      title = paste0(config$display_name, ": Horseshoe and ridge Fourier fits"),
      subtitle = sprintf(
        "True function in black; n = %d, J = %d, known noise SD = %.2f",
        options$n,
        options$fit_J,
        config$sigma
      ),
      x = "x",
      y = "Function value",
      caption = "Horseshoe: shared half-Cauchy global scale; ridge: 20-fold CV"
    ) +
    base_plot_theme()

  jpg_path <- file.path(output_dir, paste0(config$file_stem, ".jpg"))
  pdf_path <- file.path(output_dir, paste0(config$file_stem, ".pdf"))

  ggplot2::ggsave(
    filename = jpg_path,
    plot = fit_plot,
    width = 7.0,
    height = 5.2,
    dpi = 320,
    bg = "white"
  )
  ggplot2::ggsave(
    filename = pdf_path,
    plot = fit_plot,
    width = 7.0,
    height = 5.2,
    device = grDevices::cairo_pdf,
    bg = "white"
  )

  c(jpg = jpg_path, pdf = pdf_path)
}

save_mse_plot <- function(mse_long, config, output_dir) {
  mse_long$method <- factor(
    mse_long$method,
    levels = c("Horseshoe", "Ridge")
  )

  mse_plot <- ggplot2::ggplot(
    mse_long,
    ggplot2::aes(
      x = J,
      y = mse_x1000,
      color = method,
      linetype = method,
      shape = method
    )
  ) +
    ggplot2::geom_line(linewidth = 0.7) +
    ggplot2::geom_point(size = 2.2, fill = "white") +
    ggplot2::scale_x_continuous(breaks = sort(unique(mse_long$J))) +
    ggplot2::scale_color_manual(
      values = c(Horseshoe = "#2457A6", Ridge = "#D17A22")
    ) +
    ggplot2::scale_linetype_manual(
      values = c(Horseshoe = "solid", Ridge = "22")
    ) +
    ggplot2::scale_shape_manual(
      values = c(Horseshoe = 16, Ridge = 17)
    ) +
    ggplot2::labs(
      title = paste0(config$display_name, ": design-point MSE by Fourier dimension"),
      subtitle = paste0(
        "One simulated data set held fixed; Horseshoe posterior mean; ",
        "ridge penalty from 20-fold CV"
      ),
      x = "Fourier dictionary dimension J",
      y = expression(MSE %*% 10^3)
    ) +
    base_plot_theme() +
    ggplot2::theme(legend.position = "top")

  jpg_path <- file.path(
    output_dir,
    paste0(config$file_stem, "_mse_by_J.jpg")
  )
  pdf_path <- file.path(
    output_dir,
    paste0(config$file_stem, "_mse_by_J.pdf")
  )

  ggplot2::ggsave(
    filename = jpg_path,
    plot = mse_plot,
    width = 7.0,
    height = 5.2,
    dpi = 320,
    bg = "white"
  )
  ggplot2::ggsave(
    filename = pdf_path,
    plot = mse_plot,
    width = 7.0,
    height = 5.2,
    device = grDevices::cairo_pdf,
    bg = "white"
  )

  c(jpg = jpg_path, pdf = pdf_path)
}

format_latex_value <- function(value, comparator) {
  formatted <- sprintf("%.3f", value)
  if (is.finite(value) && is.finite(comparator) && value < comparator) {
    paste0("\\textbf{", formatted, "}")
  } else {
    formatted
  }
}

write_latex_rows <- function(mse_wide, config, output_dir) {
  hs_values <- mapply(
    format_latex_value,
    mse_wide$horseshoe_x1000,
    mse_wide$ridge_x1000,
    USE.NAMES = FALSE
  )
  ridge_values <- mapply(
    format_latex_value,
    mse_wide$ridge_x1000,
    mse_wide$horseshoe_x1000,
    USE.NAMES = FALSE
  )

  lines <- c(
    paste0("\\multirow{2}{*}{$f_", config$function_id, "$}"),
    paste0("& Horseshoe & ", paste(hs_values, collapse = " & "), " \\\\"),
    paste0("& Ridge & ", paste(ridge_values, collapse = " & "), " \\\\")
  )

  path <- file.path(
    output_dir,
    paste0(config$file_stem, "_table_rows.tex")
  )
  writeLines(lines, path)
  path
}

run_ridge_hs_comparison <- function(config, options, script_dir) {
  check_ridge_hs_packages()

  if (is.null(options$output_root)) {
    root_name <- if (isTRUE(options$quick)) "quick_results" else "results"
    output_root <- file.path(script_dir, root_name)
  } else {
    output_root <- normalizePath(
      options$output_root,
      winslash = "/",
      mustWork = FALSE
    )
  }

  output_dir <- file.path(
    output_root,
    paste0("function_", config$function_id)
  )
  dir.create(output_dir, recursive = TRUE, showWarnings = FALSE)

  x <- seq(0, 1, length.out = options$n)
  truth <- config$target(x)

  set.seed(config$seed)
  noise <- stats::rnorm(options$n, mean = 0, sd = config$sigma)
  y <- truth + noise

  foldid <- make_cv_folds(
    n = options$n,
    nfolds = options$nfolds,
    seed = config$seed + 101L
  )

  message(
    sprintf(
      "%s: displayed fit with n=%d and J=%d",
      config$display_name,
      options$n,
      options$fit_J
    )
  )
  display_design <- fourier_dictionary(x, options$fit_J)
  display_hs <- fit_horseshoe_fourier(
    y = y,
    design = display_design,
    sigma = config$sigma,
    burn = options$burn,
    nmc = options$nmc,
    thin = options$thin,
    seed = config$seed + 10000L + options$fit_J
  )
  display_ridge <- fit_ridge_fourier(
    y = y,
    design = display_design,
    foldid = foldid,
    nfolds = options$nfolds
  )

  predictions <- data.frame(
    x = x,
    truth = truth,
    observed = y,
    horseshoe = display_hs$fitted,
    ridge = display_ridge$fitted
  )
  predictions_path <- file.path(
    output_dir,
    paste0(config$file_stem, "_predictions.csv")
  )
  utils::write.csv(predictions, predictions_path, row.names = FALSE)

  fit_paths <- save_fit_plot(
    plot_data = predictions,
    config = config,
    options = options,
    output_dir = output_dir
  )

  display_metrics <- data.frame(
    function_id = config$function_id,
    n = options$n,
    J = options$fit_J,
    p = ncol(display_design),
    sigma = config$sigma,
    method = c("Horseshoe", "Ridge"),
    mse = c(
      mean((truth - display_hs$fitted)^2),
      mean((truth - display_ridge$fitted)^2)
    ),
    mse_x1000 = 1000 * c(
      mean((truth - display_hs$fitted)^2),
      mean((truth - display_ridge$fitted)^2)
    ),
    tau_posterior_mean = c(display_hs$tau_posterior_mean, NA_real_),
    lambda_rss = c(NA_real_, display_ridge$lambda_rss),
    lambda_per_observation = c(
      NA_real_,
      display_ridge$lambda_per_observation
    ),
    cv_mse = c(NA_real_, display_ridge$cv_mse)
  )
  display_metrics_path <- file.path(
    output_dir,
    paste0(config$file_stem, "_display_metrics.csv")
  )
  utils::write.csv(display_metrics, display_metrics_path, row.names = FALSE)

  mse_long <- NULL
  mse_wide <- NULL
  mse_paths <- character()
  latex_path <- character()

  if (!isTRUE(options$skip_grid)) {
    grid_rows <- vector("list", length(options$J_grid))

    for (index in seq_along(options$J_grid)) {
      J <- options$J_grid[index]
      message(
        sprintf(
          "%s: MSE grid %d/%d (J=%d)",
          config$display_name,
          index,
          length(options$J_grid),
          J
        )
      )

      design <- fourier_dictionary(x, J)
      hs_fit <- fit_horseshoe_fourier(
        y = y,
        design = design,
        sigma = config$sigma,
        burn = options$burn,
        nmc = options$nmc,
        thin = options$thin,
        seed = config$seed + 20000L + J
      )
      ridge_fit <- fit_ridge_fourier(
        y = y,
        design = design,
        foldid = foldid,
        nfolds = options$nfolds
      )

      grid_rows[[index]] <- data.frame(
        function_id = config$function_id,
        n = options$n,
        J = J,
        p = ncol(design),
        horseshoe_mse = mean((truth - hs_fit$fitted)^2),
        ridge_mse = mean((truth - ridge_fit$fitted)^2),
        tau_posterior_mean = hs_fit$tau_posterior_mean,
        ridge_lambda_rss = ridge_fit$lambda_rss,
        ridge_lambda_per_observation = ridge_fit$lambda_per_observation,
        ridge_cv_mse = ridge_fit$cv_mse
      )
    }

    mse_wide <- do.call(rbind, grid_rows)
    mse_wide$horseshoe_x1000 <- 1000 * mse_wide$horseshoe_mse
    mse_wide$ridge_x1000 <- 1000 * mse_wide$ridge_mse

    wide_path <- file.path(
      output_dir,
      paste0(config$file_stem, "_mse_table.csv")
    )
    utils::write.csv(mse_wide, wide_path, row.names = FALSE)

    mse_long <- rbind(
      data.frame(
        function_id = config$function_id,
        n = options$n,
        J = mse_wide$J,
        p = mse_wide$p,
        method = "Horseshoe",
        mse = mse_wide$horseshoe_mse,
        mse_x1000 = mse_wide$horseshoe_x1000
      ),
      data.frame(
        function_id = config$function_id,
        n = options$n,
        J = mse_wide$J,
        p = mse_wide$p,
        method = "Ridge",
        mse = mse_wide$ridge_mse,
        mse_x1000 = mse_wide$ridge_x1000
      )
    )
    long_path <- file.path(
      output_dir,
      paste0(config$file_stem, "_mse_long.csv")
    )
    utils::write.csv(mse_long, long_path, row.names = FALSE)

    mse_paths <- save_mse_plot(
      mse_long = mse_long,
      config = config,
      output_dir = output_dir
    )
    latex_path <- write_latex_rows(
      mse_wide = mse_wide,
      config = config,
      output_dir = output_dir
    )
  }

  signal_to_noise <- sum(truth^2) / sum(noise^2)
  summary_lines <- c(
    paste0("Ridge vs Horseshoe comparison: ", config$display_name),
    paste0("Target: ", config$formula_text),
    sprintf("Seed: %d", config$seed),
    sprintf("n: %d", options$n),
    sprintf("Displayed Fourier dimension J (= p): %d", options$fit_J),
    paste0(
      "MSE-grid Fourier dimensions J (= p): ",
      if (isTRUE(options$skip_grid)) {
        "skipped"
      } else {
        paste(options$J_grid, collapse = ", ")
      }
    ),
    sprintf("Known noise SD: %.6f", config$sigma),
    sprintf("Empirical signal-to-noise ratio: %.6f", signal_to_noise),
    "Horseshoe global-scale method: halfCauchy",
    "Horseshoe point estimate: coefficientwise posterior mean (BetaHat)",
    sprintf(
      "MCMC: burn=%d, nmc=%d, thin=%d",
      options$burn,
      options$nmc,
      options$thin
    ),
    sprintf("Ridge CV folds: %d", options$nfolds),
    paste0(
      "Ridge: direct solution of RSS + lambda*||beta||^2; ",
      "all columns, including the constant, are penalized"
    ),
    "",
    "Displayed-fit metrics:",
    capture.output(print(display_metrics, row.names = FALSE)),
    "",
    "R session:",
    capture.output(utils::sessionInfo())
  )
  summary_path <- file.path(
    output_dir,
    paste0(config$file_stem, "_summary.txt")
  )
  writeLines(summary_lines, summary_path)

  manifest <- data.frame(
    artifact = c(
      "predictions",
      "display_metrics",
      "fit_jpg",
      "fit_pdf",
      if (length(mse_paths) > 0L) {
        c("mse_table", "mse_long", "mse_jpg", "mse_pdf", "latex_rows")
      }
    ),
    path = c(
      predictions_path,
      display_metrics_path,
      unname(fit_paths["jpg"]),
      unname(fit_paths["pdf"]),
      if (length(mse_paths) > 0L) {
        c(
          wide_path,
          long_path,
          unname(mse_paths["jpg"]),
          unname(mse_paths["pdf"]),
          latex_path
        )
      }
    )
  )
  manifest$path <- normalizePath(
    manifest$path,
    winslash = "/",
    mustWork = TRUE
  )
  manifest_path <- file.path(
    output_dir,
    paste0(config$file_stem, "_manifest.csv")
  )
  utils::write.csv(manifest, manifest_path, row.names = FALSE)

  message("Finished. Results: ", normalizePath(output_dir, winslash = "/"))

  invisible(
    list(
      config = config,
      options = options,
      output_dir = output_dir,
      display_metrics = display_metrics,
      mse_table = mse_wide,
      manifest = manifest
    )
  )
}
