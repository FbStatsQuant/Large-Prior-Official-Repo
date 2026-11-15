# ============================================================
#  F2_worker.R
#  SLURM array worker: one job = one (n, seed) pair
#  Fits horseshoe for Fourier and B-spline bases
#  Saves: theta mean and median for each basis
#  Output: one .rds per job -> <this folder>/results/n<n>_s<seed>.rds
# ============================================================

library(horseshoe)
library(splines)

# ------------------------------------------------------------
#  Paths: results go to results/ next to this script,
#  unless LP_RESULTS_DIR is set.
# ------------------------------------------------------------
script_arg <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
script_dir <- if (length(script_arg) > 0L) dirname(normalizePath(sub("^--file=", "", script_arg[1L]))) else getwd()
results_root <- Sys.getenv("LP_RESULTS_DIR", unset = file.path(script_dir, "results"))

# ============================================================
#  Parse SLURM array task ID -> (n, seed)
#  Task IDs: 1 to 5900
#  n_seq has 59 values, seed_seq has 100 values
#  task_id = (i_n - 1) * 100 + i_seed
# ============================================================
args    <- commandArgs(trailingOnly = TRUE)
if (length(args) != 1L) stop("Expected exactly one SLURM array task ID.")
task_id <- suppressWarnings(as.integer(args[1]))

n_seq    <- seq(1000, 30000, by = 500)  
seed_seq <- 1:100                          
n_seeds  <- length(seed_seq)
n_tasks  <- length(n_seq) * n_seeds

if (is.na(task_id) || task_id < 1L || task_id > n_tasks) {
  stop(sprintf("Task ID must be between 1 and %d.", n_tasks))
}

i_n    <- (task_id - 1) %/% n_seeds + 1
i_seed <- (task_id - 1) %%  n_seeds + 1

n    <- n_seq[i_n]
seed <- seed_seq[i_seed]

cat(sprintf("[Task %d] n = %d | seed = %d\n", task_id, n, seed))

# ============================================================
#  Skip work that is already on disk
#  Lets F2_array.slurm be re-submitted to fill in a partial run
#  without recomputing completed (n, seed) pairs.
#  Set F2_FORCE=1 to recompute regardless.
# ============================================================
out_dir  <- results_root
out_file <- file.path(out_dir, sprintf("n%d_s%d.rds", n, seed))

if (file.exists(out_file) && !nzchar(Sys.getenv("F2_FORCE"))) {
  cat(sprintf("  Already done: %s -- skipping.\n", out_file))
  quit(save = "no", status = 0)
}

# ============================================================
#  Settings
# ============================================================
sd_val <- 0.07
b      <- 0.7
J      <- floor(n^b)

frac <- function(x) x - floor(x)
B4   <- function(t) t^4 - 2*t^3 + t^2 - 1/30
f <- function(x) 2.25 * B4(frac(x - 0.1)) - 7.5 * B4(frac(x - 0.4))  # pp ~ 0.53

# ============================================================
#  Basis constructors
# ============================================================
fourier_basis <- function(x, K) {
  basis <- matrix(1, nrow = length(x), ncol = K + 1)
  for (k in 1:K) basis[, k + 1] <- cos(pi * k * x)
  basis
}

bspline_basis <- function(x, K) {
  bs(x, df = K, degree = 3, intercept = TRUE)
}

# ============================================================
#  Generate data
# ============================================================
set.seed(seed)
x <- seq(0, 1, length.out = n)
y <- f(x) + rnorm(n, mean = 0, sd = sd_val)

# ============================================================
#  Fit horseshoe — Fourier
# ============================================================
cat("  Fitting Fourier...\n")
B_fourier <- fourier_basis(x, J)

Hs_fourier <- horseshoe(y, B_fourier,
                        method.tau   = "fixed",
                        tau          = 1 / (n^0.9),
                        method.sigma = "fixed",
                        Sigma2       = sd_val^2,
                        nmc          = 5000,
                        burn         = 2000)

theta_mean_fourier   <- Hs_fourier$BetaHat      # posterior mean of theta
theta_median_fourier <- Hs_fourier$BetaMedian   # posterior median of theta

cat(sprintf("  Fourier done. theta length: %d\n", length(theta_mean_fourier)))

# ============================================================
#  Fit horseshoe — B-spline
# ============================================================
cat("  Fitting B-spline...\n")
B_spline <- bspline_basis(x, J)

Hs_spline <- horseshoe(y, B_spline,
                       method.tau   = "halfCauchy",
                       tau          = 1 / n,
                       method.sigma = "fixed",
                       Sigma2       = sd_val^2,
                       nmc          = 5000,
                       burn         = 2000)

theta_mean_spline   <- Hs_spline$BetaHat
theta_median_spline <- Hs_spline$BetaMedian

cat(sprintf("  B-spline done. theta length: %d\n", length(theta_mean_spline)))

# ============================================================
#  Save results
# ============================================================
result <- list(
  n                    = n,
  seed                 = seed,
  J                    = J,
  theta_mean_fourier   = theta_mean_fourier,
  theta_median_fourier = theta_median_fourier,
  theta_mean_spline    = theta_mean_spline,
  theta_median_spline  = theta_median_spline
)

dir.create(out_dir, showWarnings = FALSE, recursive = TRUE)
saveRDS(result, file = out_file)
cat(sprintf("  Saved: %s\n", out_file))
