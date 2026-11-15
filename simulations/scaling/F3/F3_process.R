# ============================================================
#  F3_process.R
#  Reads all .rds files from <this folder>/results/
#  Expected fresh-run grid: n = 400, 800, ..., 14800; seed = 1, ..., 100.
#  Computes per (n, seed):
#    - RMSE using mean vector
#    - RMSE using median vector
#    - a1: # coefficients > 1/sqrt(J)
#    - a2: # coefficients > 1/J
#    - a3: # coefficients > 1/(J*sqrt(n))
#  Saves two CSVs to <this folder>/processed/:
#    - F3_fourier.csv
#    - F3_spline.csv
# ============================================================

# ------------------------------------------------------------
#  Paths: reads results/ and writes processed/ next to this
#  script, unless LP_RESULTS_DIR / LP_PROCESSED_DIR are set.
# ------------------------------------------------------------
script_arg <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
script_dir <- if (length(script_arg) > 0L) dirname(normalizePath(sub("^--file=", "", script_arg[1L]))) else getwd()
results_root <- Sys.getenv("LP_RESULTS_DIR", unset = file.path(script_dir, "results"))
processed_root <- Sys.getenv("LP_PROCESSED_DIR", unset = file.path(script_dir, "processed"))

# ============================================================
#  True function
# ============================================================
frac <- function(x) x - floor(x)
B6   <- function(t) t^6 - 3*t^5 + 2.5*t^4 - 0.5*t^2 + 1/42
f_true <- function(x) 2 * B6(frac(x - 0.2)) + 8 * B6(frac(x - 0.5)) - 2 * B6(frac(x - 0.9))  # pp ~ 0.45

# ============================================================
#  Load all .rds files
# ============================================================
results_dir <- results_root
files       <- list.files(path        = results_dir,
                          pattern     = "\\.rds$",
                          full.names  = TRUE)

if (length(files) == 0L) stop("No result files found; check the input directory and run the worker first.")
cat(sprintf("Found %d .rds files\n", length(files)))

# ============================================================
#  Pre-allocate output data frames
# ============================================================
n_files <- length(files)

fourier_df <- data.frame(
  n           = integer(n_files),
  seed        = integer(n_files),
  J           = integer(n_files),
  rmse_mean   = numeric(n_files),
  rmse_median = numeric(n_files),
  a1          = integer(n_files),
  a2          = integer(n_files),
  a3          = integer(n_files)
)

spline_df <- fourier_df

# ============================================================
#  Main loop
# ============================================================
for (i in seq_along(files)) {

  res  <- readRDS(files[i])
  n    <- res$n
  seed <- res$seed
  J    <- res$J

  x      <- seq(0, 1, length.out = n)
  y_true <- f_true(x)

  # --- thresholds -------------------------------------------
  thr1 <- 1 / sqrt(J)       # a1
  thr2 <- 1 / J             # a2
  thr3 <- 1 / (J * sqrt(n)) # a3

  # --- Fourier -----------------------------------------------
  yhat_mean_f   <- as.vector(res$theta_mean_fourier)
  yhat_median_f <- as.vector(res$theta_median_fourier)

  # fitted values: X %*% theta  — but we only stored theta, not X
  # Reconstruct basis to get fitted values
  B_f <- matrix(1, nrow = n, ncol = J + 1)
  for (k in 1:J) B_f[, k + 1] <- cos(pi * k * x)

  fitted_mean_f   <- B_f %*% yhat_mean_f
  fitted_median_f <- B_f %*% yhat_median_f

  rmse_mean_f   <- sqrt(mean((fitted_mean_f   - y_true)^2))
  rmse_median_f <- sqrt(mean((fitted_median_f - y_true)^2))

  a1_f <- sum(abs(yhat_mean_f) > thr1)
  a2_f <- sum(abs(yhat_mean_f) > thr2)
  a3_f <- sum(abs(yhat_mean_f) > thr3)

  fourier_df[i, ] <- list(n, seed, J,
                          rmse_mean_f, rmse_median_f,
                          a1_f, a2_f, a3_f)

  # --- B-spline ----------------------------------------------
  library(splines)
  yhat_mean_s   <- as.vector(res$theta_mean_spline)
  yhat_median_s <- as.vector(res$theta_median_spline)

  B_s <- bs(x, df = J, degree = 3, intercept = TRUE)

  fitted_mean_s   <- B_s %*% yhat_mean_s
  fitted_median_s <- B_s %*% yhat_median_s

  rmse_mean_s   <- sqrt(mean((fitted_mean_s   - y_true)^2))
  rmse_median_s <- sqrt(mean((fitted_median_s - y_true)^2))

  a1_s <- sum(abs(yhat_mean_s) > thr1)
  a2_s <- sum(abs(yhat_mean_s) > thr2)
  a3_s <- sum(abs(yhat_mean_s) > thr3)

  spline_df[i, ] <- list(n, seed, J,
                         rmse_mean_s, rmse_median_s,
                         a1_s, a2_s, a3_s)

  if (i %% 100 == 0) cat(sprintf("  Processed %d / %d\n", i, n_files))
}

# ============================================================
#  Sort by n then seed
# ============================================================
fourier_df <- fourier_df[order(fourier_df$n, fourier_df$seed), ]
spline_df  <- spline_df[order(spline_df$n,  spline_df$seed),  ]

# ============================================================
#  Save CSVs
# ============================================================
out_dir <- processed_root
dir.create(out_dir, showWarnings = FALSE, recursive = TRUE)

write.csv(fourier_df, file = file.path(out_dir, "F3_fourier.csv"), row.names = FALSE)
write.csv(spline_df,  file = file.path(out_dir, "F3_spline.csv"),  row.names = FALSE)

cat(sprintf("\nDone. Files saved to %s\n", out_dir))
cat(sprintf("  F3_fourier.csv : %d rows\n", nrow(fourier_df)))
cat(sprintf("  F3_spline.csv  : %d rows\n", nrow(spline_df)))
