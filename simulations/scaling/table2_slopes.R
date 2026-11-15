# =====================================================================
# table2_slopes.R -- the log-log slopes of Table 2 (Section 3.2),
# computed from the processed CSVs written by F*_process.R.
#
# Rules (Section 3.2 of the paper):
#   - at each n, take the median across data sets of
#       RMSE   (column rmse_mean: the posterior-mean estimate) and
#       q_hat  (column a2: number of |posterior-mean coefficients| > 1/J_n);
#   - grid n = 1000, 1500, ..., 20000;
#   - Raw      = OLS slope of log(median RMSE) on log(n);
#   - Adjusted = OLS slope of log(median RMSE) - 0.5 log(log n) on log(n);
#   - gamma_q  = OLS slope of log(median q_hat) on log(n).
#
# Usage (from this folder):
#   Rscript table2_slopes.R                    # reads F*/processed/F*_{fourier,spline}.csv
#   Rscript table2_slopes.R --processed=reference_outputs/F1 --functions=F1
#   Options: --nmin=1000 --nmax=20000 --functions=F1,F2,F3 --processed=<folder>
#   With --processed=<folder>, every CSV is read from that one folder.
# =====================================================================

script_arg <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
script_dir <- if (length(script_arg) > 0L) dirname(normalizePath(sub("^--file=", "", script_arg[1L]))) else getwd()

args <- commandArgs(trailingOnly = TRUE)
opt  <- function(name, default) {
  hit <- grep(paste0("^--", name, "="), args, value = TRUE)
  if (length(hit) == 0L) default else sub(paste0("^--", name, "="), "", hit[length(hit)])
}
nmin      <- as.numeric(opt("nmin", 1000))
nmax      <- as.numeric(opt("nmax", 20000))
functions <- strsplit(opt("functions", "F1,F2,F3"), ",", fixed = TRUE)[[1L]]
processed <- opt("processed", "")

csv_path <- function(f, basis) {
  file <- sprintf("%s_%s.csv", f, basis)
  if (nzchar(processed)) file.path(processed, file) else file.path(script_dir, f, "processed", file)
}

slope <- function(y, n) unname(coef(lm(y ~ log(n)))[2L])

rows <- list()
for (f in functions) {
  for (basis in c("spline", "fourier")) {
    path <- csv_path(f, basis)
    if (!file.exists(path)) { cat("missing:", path, "\n"); next }
    d <- read.csv(path)
    d <- d[d$n >= nmin & d$n <= nmax, ]
    if (nrow(d) == 0L) { cat("no rows in range:", path, "\n"); next }
    per_n <- do.call(rbind, lapply(split(d, d$n), function(g) data.frame(
      n = g$n[1L], seeds = nrow(g),
      rmse = median(g$rmse_mean), q = median(g$a2))))
    per_n <- per_n[order(per_n$n), ]
    if (nrow(per_n) < 2L) { cat("fewer than two n values:", path, "\n"); next }
    rows[[length(rows) + 1L]] <- data.frame(
      f        = f,
      basis    = if (basis == "spline") "B-spline" else "Cosine",
      n_values = nrow(per_n),
      seeds    = paste(range(per_n$seeds), collapse = "-"),
      raw      = round(slope(log(per_n$rmse), per_n$n), 3),
      adjusted = round(slope(log(per_n$rmse) - 0.5 * log(log(per_n$n)), per_n$n), 3),
      gamma_q  = if (all(per_n$q > 0)) round(slope(log(per_n$q), per_n$n), 3) else NA_real_)
  }
}

if (length(rows) == 0L) stop("no slopes computed (CSV files missing, or fewer than two n values in range)")
out <- do.call(rbind, rows)
cat(sprintf("Slopes on n in [%g, %g] (median across seeds at each n)\n", nmin, nmax))
print(out, row.names = FALSE)
