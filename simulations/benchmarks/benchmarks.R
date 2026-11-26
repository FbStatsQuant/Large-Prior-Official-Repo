# benchmarks.R: finite-sample comparison of least squares, cross-validated ridge and the Horseshoe (paper Section 3.2, Table 1, Figure 2).
# Two targets, each with its own dictionary and design, at n = 1000 and J = 140, 160, ..., 300:
#   f1 with the real Fourier dictionary on the equally spaced design (noise sd 0.15),
#   f2 with the Chebyshev dictionary on the Gauss-Chebyshev nodes (noise sd 0.20).
# One simulated response per target, reused for every J and every method. Then the two Horseshoe fits at J = floor(n^0.7) = 125 for Figure 2.
#   Rscript benchmarks.R            paper settings; writes results/
#   Rscript benchmarks.R --quick    J = 140 and 160 only, 200 burn-in and 500 saved sweeps; writes quick_results/
#   --out=DIR                       write to DIR instead
# Figure 2 is drawn from display_points.csv and display_metrics.csv by make_figure.R.
options(warn = 1)
here <- local({ a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
                if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd() })
source(file.path(here, "..", "common.R"))
source(file.path(here, "ridge.R"))

args  <- commandArgs(trailingOnly = TRUE)
quick <- "--quick" %in% args
out   <- sub("^--out=", "", grep("^--out=", args, value = TRUE))
out   <- if (length(out) == 1L) out else file.path(here, if (quick) "quick_results" else "results")
dir.create(out, showWarnings = FALSE, recursive = TRUE)

# ---- settings
N <- 1000L
J_GRID <- if (quick) c(140L, 160L) else seq.int(140L, 300L, by = 20L)
J_DISPLAY <- J_of_n(N); stopifnot(J_DISPLAY == 125L)
BURN <- if (quick) 200L else 2000L
NMC  <- if (quick) 500L else 5000L
NFOLDS <- 20L                                                # ridge: 20-fold CV over 160 penalties (see ridge.R)
DATA_SEED <- 1L; MCMC_SEED <- 1001L; FOLD_SEED <- 2001L
PAIRS <- CELLS[CELLS$id %in% c("f1_fourier", "f2_chebyshev"), ]
stopifnot(nrow(PAIRS) == 2L)
METHODS <- c("OLS", "Ridge", "Horseshoe")

# ---- data shared by both targets, every J and every method; the CV folds are shared too
set.seed(DATA_SEED); z <- rnorm(N)
foldid <- make_cv_folds(n = N, nfolds = NFOLDS, seed = FOLD_SEED)

long <- list(); diag_rows <- list(); k <- 0L
for (ci in seq_len(nrow(PAIRS))) {
  cell <- PAIRS[ci, ]
  for (J in J_GRID) {
    b <- build_cell(cell, N, J, z); X <- b$X; y <- b$y; f0 <- b$f0
    # OLS: no prior; full column rank asserted
    qx <- qr(X)
    if (qx$rank != J) stop(sprintf("%s J=%d: OLS design is rank deficient (rank %d)", cell$id, J, qx$rank))
    b_ols <- qr.coef(qx, y); f_ols <- drop(X %*% b_ols)
    # ridge: 20-fold CV, penalty on every column including the constant
    rf <- fit_ridge_fourier(y = y, design = X, foldid = foldid, nfolds = NFOLDS)
    # Horseshoe: half-Cauchy scale, sigma known; set.seed(MCMC_SEED) immediately before hs_fast() inside fit_horseshoe()
    hs <- fit_horseshoe(cell, N, J, b, MCMC_SEED, burn = BURN, nmc = NMC)
    mse <- c(OLS = mean((f_ols - f0)^2), Ridge = mean((rf$fitted - f0)^2), Horseshoe = hs$rmse_design^2)
    if (!all(is.finite(mse)) || any(mse <= 0)) stop(sprintf("%s J=%d: non-finite or non-positive MSE", cell$id, J))
    long[[length(long) + 1L]] <- data.frame(target = cell$fun, dictionary = cell$basis, J = J, method = METHODS, mse = unname(mse[METHODS]),
                                            mse_x1000 = 1000 * unname(mse[METHODS]), stringsAsFactors = FALSE)
    grid_edge <- rf$lambda_rss %in% range(max(diag(crossprod(X))) * 10^seq(4, -8, length.out = 160L))
    k <- k + 1L
    diag_rows[[k]] <- data.frame(target = cell$fun, J = J, lambda_rss = rf$lambda_rss, lambda_per_obs = rf$lambda_per_observation,
                                 cv_mse = rf$cv_mse, lambda_at_grid_edge = grid_edge, structure = hs$structure, tau_hat = hs$tau_hat,
                                 mcse_rel = hs$mcse_rel, ess_f_min = min(hs$ess_fpts), rhat1_f_max = max(hs$rhat1_f), ess_logtau = hs$ess_logtau,
                                 hs_seconds = hs$hs_fast_wall, stringsAsFactors = FALSE)
    cat(sprintf("%s J=%d  MSE x1e3: OLS %.3f  Ridge %.3f  Horseshoe %.3f\n", cell$fun, J, 1e3 * mse[["OLS"]], 1e3 * mse[["Ridge"]], 1e3 * mse[["Horseshoe"]]))
    rm(b, X); invisible(gc())
  }
}
mse_long <- do.call(rbind, long); rownames(mse_long) <- NULL
dg <- do.call(rbind, diag_rows); rownames(dg) <- NULL
write.csv(mse_long, file.path(out, "mse_long.csv"), row.names = FALSE)

# ---- Table 1: one row per target and method, one column per J (values multiplied by 1000)
mse_table <- do.call(rbind, lapply(PAIRS$fun, function(tg) do.call(rbind, lapply(METHODS, function(m) {
  d <- mse_long[mse_long$target == tg & mse_long$method == m, ]; d <- d[order(d$J), ]
  row <- data.frame(target = tg, method = m, stringsAsFactors = FALSE)
  for (i in seq_len(nrow(d))) row[[paste0("J", d$J[i])]] <- d$mse_x1000[i]
  row }))))
rownames(mse_table) <- NULL
write.csv(mse_table, file.path(out, "mse_table.csv"), row.names = FALSE)

# ---- table_rows.tex: the body of Table 1; the lowest value in each column of each target is bold
jcols <- paste0("J", J_GRID)
tex <- character(0)
for (tg in PAIRS$fun) {
  d <- mse_table[mse_table$target == tg, ]
  best <- apply(as.matrix(d[jcols]), 2, which.min)
  tex <- c(tex, sprintf("\\multirow{3}{*}{$%s_%s$}", substr(tg, 1, 1), substr(tg, 2, 2)))
  for (r in seq_len(nrow(d))) {
    cells_tex <- vapply(seq_along(jcols), function(i) { s <- sprintf("%.3f", d[[jcols[i]]][r]); if (best[i] == r) sprintf("\\textbf{%s}", s) else s }, "")
    tex <- c(tex, sprintf("& %s", d$method[r]), sprintf("& %s \\\\", paste(cells_tex, collapse = " & ")))
  }
  if (tg != PAIRS$fun[nrow(PAIRS)]) tex <- c(tex, "\\midrule")
}
writeLines(tex, file.path(out, "table_rows.tex"))

# ---- Figure 2: Horseshoe fits at J = floor(n^0.7) = 125 on the same data (panel a: f1, Fourier; panel b: f2, Chebyshev)
pts <- list(); met <- list()
for (ci in seq_len(nrow(PAIRS))) {
  cell <- PAIRS[ci, ]; panel_id <- c("a", "b")[ci]
  b <- build_cell(cell, N, J_DISPLAY, z)
  hs <- fit_horseshoe(cell, N, J_DISPLAY, b, MCMC_SEED, burn = BURN, nmc = NMC)
  fitted <- drop(b$X %*% hs$beta_hat)
  pts[[ci]] <- data.frame(panel = panel_id, x = b$x, truth = b$f0, fitted = fitted)
  met[[ci]] <- data.frame(panel = panel_id, target = cell$fun, dictionary = cell$basis, J = J_DISPLAY, mse = hs$rmse_design^2,
                          mse_x1000 = 1000 * hs$rmse_design^2, stringsAsFactors = FALSE)
  cat(sprintf("display %s J=%d  Horseshoe MSE x1e3 = %.3f\n", cell$fun, J_DISPLAY, 1000 * hs$rmse_design^2))
  rm(b); invisible(gc())
}
write.csv(do.call(rbind, pts), file.path(out, "display_points.csv"), row.names = FALSE)
write.csv(do.call(rbind, met), file.path(out, "display_metrics.csv"), row.names = FALSE)

# ---- summary.txt
si <- capture.output(print(sessionInfo())); si <- si[!grepl("^(BLAS|LAPACK)", si)]      # drop library paths
fits_txt <- sprintf("  %s  J=%3d  Horseshoe: Gram form %-7s tau_hat %.5g  ESS(log tau) %5.0f  min ESS(f at 5 points) %5.0f  max split-Rhat %.4f  MCSE/RMSE %.4f  seconds %.1f",
                    dg$target, dg$J, dg$structure, dg$tau_hat, dg$ess_logtau, dg$ess_f_min, dg$rhat1_f_max, dg$mcse_rel, dg$hs_seconds)
ridge_txt <- sprintf("  %s  J=%3d  lambda (on the RSS scale) %.6g, per observation %.6g; CV mean squared error %.6g; at an end of the penalty grid: %s",
                     dg$target, dg$J, dg$lambda_rss, dg$lambda_per_obs, dg$cv_mse, ifelse(dg$lambda_at_grid_edge, "yes", "no"))
dm <- do.call(rbind, met)
txt <- c(
  "Benchmark of OLS, cross-validated ridge and the Horseshoe (paper Section 3.2, Table 1 and Figure 2)", "",
  "Settings",
  sprintf("  n = %d; J = %s; display fits at J = floor(n^0.7) = %d", N, paste(J_GRID, collapse = ", "), J_DISPLAY),
  "  f1: Fourier dictionary, equispaced design, noise sd 0.15;  f2: Chebyshev dictionary, Gauss-Chebyshev nodes, noise sd 0.20",
  sprintf("  data: z = {set.seed(%d); rnorm(n)}, shared by both targets, every J and every method; y = f(x) + sigma z", DATA_SEED),
  sprintf("  Horseshoe: half-Cauchy scale (start 1), sigma known, %d burn-in and %d saved sweeps, floor exact, structure auto; set.seed(%d) just before every hs_fast()", BURN, NMC, MCMC_SEED),
  sprintf("  ridge: minimizes ||y - X b||^2 + lambda ||b||^2 (constant penalized); %d-fold CV over 160 penalties; folds from make_cv_folds(n, %d, %d)", NFOLDS, NFOLDS, FOLD_SEED),
  "  OLS: QR, full column rank asserted",
  "  error: design-point MSE, (1/n) sum_i (f_hat(x_i) - f(x_i))^2; tables show MSE x 1000",
  sprintf("  mode: %s", if (quick) "quick (reduced grid and chain: the numbers are not those of the paper)" else "paper settings"), "",
  "MSE x 1000 (rows of Table 1)",
  sprintf("  %-3s %-10s %s", mse_table$target, mse_table$method, vapply(seq_len(nrow(mse_table)), function(r) paste(sprintf("%7.3f", unlist(mse_table[r, jcols])), collapse = " "), "")),
  sprintf("  columns: J = %s", paste(J_GRID, collapse = " ")), "",
  "Figure 2: Horseshoe fits at J = 125, MSE x 1000",
  sprintf("  %s (%s): %.3f", dm$target, dm$dictionary, dm$mse_x1000), "",
  "Ridge penalties chosen", ridge_txt, "",
  "Horseshoe diagnostics per fit (design-point MSE; ESS = effective sample size; Rhat = single-chain split R-hat of the fitted value at five design points)", fits_txt, "",
  "R session", si)
writeLines(txt, file.path(out, "summary.txt"))
cat(sprintf("\nWrote %s/\n", basename(out)))
