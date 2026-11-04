script_arg <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
script_dir <- if (length(script_arg) > 0L) {
  dirname(normalizePath(sub("^--file=", "", script_arg[1L]), mustWork = TRUE))
} else {
  normalizePath(getwd(), mustWork = TRUE)
}

if (!requireNamespace("ggplot2", quietly = TRUE)) {
  stop("The ggplot2 package is required.", call. = FALSE)
}

results_dir <- file.path(script_dir, "results")
output_dir <- file.path(script_dir, "trend_plots")
dir.create(output_dir, recursive = TRUE, showWarnings = FALSE)

panel_labels <- c(
  "(a)  f1, nominal order 1",
  "(b)  f2, nominal order 3",
  "(c)  f3, nominal order 5"
)

prediction_sets <- vector("list", 3L)
metric_sets <- vector("list", 3L)

for (function_id in 1:3) {
  function_dir <- file.path(
    results_dir,
    paste0("function_", function_id)
  )
  prediction_path <- file.path(
    function_dir,
    paste0("f", function_id, "_predictions.csv")
  )
  metric_path <- file.path(
    function_dir,
    paste0("f", function_id, "_display_metrics.csv")
  )

  if (!file.exists(prediction_path) || !file.exists(metric_path)) {
    stop(
      "Missing full-run results for function ",
      function_id,
      ". Run function_",
      function_id,
      ".R before creating the trend plots.",
      call. = FALSE
    )
  }

  predictions <- utils::read.csv(prediction_path)
  metrics <- utils::read.csv(metric_path)

  required_prediction_columns <- c(
    "x",
    "truth",
    "observed",
    "horseshoe",
    "ridge"
  )
  if (!all(required_prediction_columns %in% names(predictions))) {
    stop(
      prediction_path,
      " does not contain the required prediction columns.",
      call. = FALSE
    )
  }

  predictions$function_id <- function_id
  predictions$panel <- panel_labels[function_id]
  prediction_sets[[function_id]] <- predictions

  hs_mse <- metrics$mse[metrics$method == "Horseshoe"]
  ridge_mse <- metrics$mse[metrics$method == "Ridge"]
  if (length(hs_mse) != 1L || length(ridge_mse) != 1L) {
    stop(
      metric_path,
      " must contain one Horseshoe row and one Ridge row.",
      call. = FALSE
    )
  }

  metric_sets[[function_id]] <- data.frame(
    function_id = function_id,
    panel = panel_labels[function_id],
    hs_mse_x1000 = 1000 * hs_mse,
    ridge_mse_x1000 = 1000 * ridge_mse,
    label = sprintf(
      "MSE x 10^3:  HS %.3f   Ridge %.3f",
      1000 * hs_mse,
      1000 * ridge_mse
    )
  )
}

all_predictions <- do.call(rbind, prediction_sets)
all_metrics <- do.call(rbind, metric_sets)
all_predictions$panel <- factor(
  all_predictions$panel,
  levels = panel_labels
)
all_metrics$panel <- factor(all_metrics$panel, levels = panel_labels)

# Plot every second design point, matching the point-estimate style of the
# original paper figure while keeping dense oscillations visible.
point_sets <- lapply(
  prediction_sets,
  function(data) data[seq.int(1L, nrow(data), by = 2L), , drop = FALSE]
)
point_predictions <- do.call(rbind, point_sets)
point_predictions$panel <- factor(
  point_predictions$panel,
  levels = panel_labels
)

method_points <- rbind(
  data.frame(
    x = point_predictions$x,
    estimate = point_predictions$horseshoe,
    method = "Horseshoe",
    function_id = point_predictions$function_id,
    panel = point_predictions$panel
  ),
  data.frame(
    x = point_predictions$x,
    estimate = point_predictions$ridge,
    method = "Ridge",
    function_id = point_predictions$function_id,
    panel = point_predictions$panel
  )
)
method_points$method <- factor(
  method_points$method,
  levels = c("Horseshoe", "Ridge")
)

method_colors <- c(
  Horseshoe = "#2457A6",
  Ridge = "#8EC7DD"
)
method_shapes <- c(
  Horseshoe = 16,
  Ridge = 1
)

paper_theme <- function(base_size = 10) {
  ggplot2::theme_minimal(base_size = base_size) +
    ggplot2::theme(
      panel.grid.minor = ggplot2::element_blank(),
      panel.grid.major = ggplot2::element_line(
        color = "#E6E6E6",
        linewidth = 0.3
      ),
      axis.title = ggplot2::element_text(color = "#222222"),
      axis.text = ggplot2::element_text(color = "#4D4D4D"),
      plot.title = ggplot2::element_text(
        face = "bold",
        color = "#1A1A1A"
      ),
      plot.subtitle = ggplot2::element_text(color = "#444444"),
      legend.title = ggplot2::element_blank(),
      legend.position = "bottom",
      strip.background = ggplot2::element_blank(),
      strip.text = ggplot2::element_text(
        face = "plain",
        size = ggplot2::rel(1.05),
        color = "#222222"
      )
    )
}

make_individual_plot <- function(function_id) {
  full_data <- prediction_sets[[function_id]]
  plot_points <- method_points[
    method_points$function_id == function_id,
    ,
    drop = FALSE
  ]
  metrics <- metric_sets[[function_id]]

  ggplot2::ggplot() +
    ggplot2::geom_line(
      data = full_data,
      ggplot2::aes(x = x, y = truth),
      color = "#202020",
      linewidth = 0.75
    ) +
    ggplot2::geom_point(
      data = plot_points,
      ggplot2::aes(
        x = x,
        y = estimate,
        color = method,
        shape = method
      ),
      size = 0.8,
      alpha = 0.9,
      stroke = 0.55
    ) +
    ggplot2::scale_color_manual(values = method_colors) +
    ggplot2::scale_shape_manual(values = method_shapes) +
    ggplot2::labs(
      title = paste0(
        "Function ",
        function_id,
        ": true trend, Horseshoe, and ridge"
      ),
      subtitle = sprintf(
        "n = 1000, J = 125; MSE x 10^3: Horseshoe %.3f, ridge %.3f",
        metrics$hs_mse_x1000,
        metrics$ridge_mse_x1000
      ),
      x = "x",
      y = "Function value"
    ) +
    paper_theme(base_size = 11)
}

individual_paths <- character()
for (function_id in 1:3) {
  individual_plot <- make_individual_plot(function_id)
  jpg_path <- file.path(output_dir, paste0("f", function_id, ".jpg"))
  pdf_path <- file.path(output_dir, paste0("f", function_id, ".pdf"))

  ggplot2::ggsave(
    filename = jpg_path,
    plot = individual_plot,
    width = 6.4,
    height = 4.8,
    dpi = 320,
    bg = "white"
  )
  ggplot2::ggsave(
    filename = pdf_path,
    plot = individual_plot,
    width = 6.4,
    height = 4.8,
    device = grDevices::cairo_pdf,
    bg = "white"
  )

  individual_paths <- c(individual_paths, jpg_path, pdf_path)
}

combined_plot <- ggplot2::ggplot() +
  ggplot2::geom_line(
    data = all_predictions,
    ggplot2::aes(x = x, y = truth),
    color = "#202020",
    linewidth = 0.65
  ) +
  ggplot2::geom_point(
    data = method_points,
    ggplot2::aes(
      x = x,
      y = estimate,
      color = method,
      shape = method
    ),
    size = 0.55,
    alpha = 0.88,
    stroke = 0.45
  ) +
  ggplot2::geom_label(
    data = all_metrics,
    ggplot2::aes(x = 0.02, y = Inf, label = label),
    inherit.aes = FALSE,
    hjust = 0,
    vjust = 1.2,
    size = 2.35,
    linewidth = 0,
    label.padding = grid::unit(0.12, "lines"),
    fill = grDevices::adjustcolor("white", alpha.f = 0.82),
    color = "#333333"
  ) +
  ggplot2::scale_color_manual(values = method_colors) +
  ggplot2::scale_shape_manual(values = method_shapes) +
  ggplot2::facet_wrap(
    facets = ggplot2::vars(panel),
    nrow = 1,
    scales = "free_y",
    strip.position = "bottom"
  ) +
  ggplot2::labs(
    title = "Horseshoe and ridge fits for the revised benchmark functions",
    subtitle = "True function in black; n = 1000 and Fourier dimension J = 125",
    x = "x",
    y = "Function value"
  ) +
  paper_theme(base_size = 10) +
  ggplot2::theme(
    strip.placement = "outside",
    panel.spacing.x = grid::unit(0.7, "lines"),
    legend.position = "top",
    plot.margin = ggplot2::margin(8, 12, 8, 8)
  )

combined_jpg <- file.path(
  output_dir,
  "ridge_hs_trend_comparison.jpg"
)
combined_pdf <- file.path(
  output_dir,
  "ridge_hs_trend_comparison.pdf"
)
paper_combined_jpg <- file.path(
  output_dir,
  "ridge_hs_trend_comparison_paper.jpg"
)
paper_combined_pdf <- file.path(
  output_dir,
  "ridge_hs_trend_comparison_paper.pdf"
)

ggplot2::ggsave(
  filename = combined_jpg,
  plot = combined_plot,
  width = 12.0,
  height = 4.3,
  dpi = 320,
  bg = "white"
)
ggplot2::ggsave(
  filename = combined_pdf,
  plot = combined_plot,
  width = 12.0,
  height = 4.3,
  device = grDevices::cairo_pdf,
  bg = "white"
)

paper_combined_plot <- combined_plot +
  ggplot2::labs(title = NULL, subtitle = NULL) +
  ggplot2::theme(
    legend.position = "top",
    plot.margin = ggplot2::margin(2, 8, 4, 4)
  )

ggplot2::ggsave(
  filename = paper_combined_jpg,
  plot = paper_combined_plot,
  width = 12.0,
  height = 3.55,
  dpi = 320,
  bg = "white"
)
ggplot2::ggsave(
  filename = paper_combined_pdf,
  plot = paper_combined_plot,
  width = 12.0,
  height = 3.55,
  device = grDevices::cairo_pdf,
  bg = "white"
)

manifest <- data.frame(
  artifact = c(
    "function_1_jpg",
    "function_1_pdf",
    "function_2_jpg",
    "function_2_pdf",
    "function_3_jpg",
    "function_3_pdf",
    "combined_jpg",
    "combined_pdf",
    "paper_combined_jpg",
    "paper_combined_pdf"
  ),
  path = normalizePath(
    c(
      individual_paths,
      combined_jpg,
      combined_pdf,
      paper_combined_jpg,
      paper_combined_pdf
    ),
    winslash = "/",
    mustWork = TRUE
  )
)
utils::write.csv(
  manifest,
  file.path(output_dir, "trend_plot_manifest.csv"),
  row.names = FALSE
)

message(
  "Trend comparison plots written to ",
  normalizePath(output_dir, winslash = "/")
)
