# =====================================================================
# Real-data applications (METHODS_SPEC.md version 3, Sections 1 and 4):
#   sunspots (cosine dictionary (M4)), bike (cosine (M4)), buoy (Fourier (M2)).
# For each series: read data/<name>.csv (columns t, x, y), fit the dictionary
# with the fixed-scale horseshoe (M1)-(M4) on the n original points, write
#   output/<name>_fit.csv      (t, x, y, fhat, lo, hi)
#   output/<name>_summary.txt  (n, K, dictionary, columns, tau, nmc, burn, seed,
#                               E[sigma|y], active frequencies and count,
#                               run time, sha256 of the input data file)
# Runs with non-default nmc or burn write to output/_quick/ instead.
#
# Usage (from any working directory):
#   Rscript run_applications.R                      # all three, nmc = 20000, burn = 10000
#   Rscript run_applications.R bike buoy            # only these (also "bike,buoy")
#   Rscript run_applications.R sunspots --nmc=500 --burn=100   # quick test -> output/_quick/
# =====================================================================

# Locate this script's folder and load the shared helpers (common.R); the
# data_applications/ root is found from there (or from LP_APP_ROOT).
local({
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  d <- if (length(a)) dirname(sub("^--file=", "", a[1L])) else file.path(Sys.getenv("LP_APP_ROOT", "."), "code")
  source(file.path(d, "common.R"))
})
root <- app_root()

source(file.path(root, "code", "fourier_hs.R"))
library(digest)   # also loaded by common.R

## ---------------------------------------------------------------------
## 1. The three applications and the command-line options
## ---------------------------------------------------------------------
apps <- data.frame(name       = c("sunspots", "bike",   "buoy"),
                   dictionary = c("cosine",   "cosine", "fourier"))

# spec defaults (burn = 10000, nmc = 20000) are the defaults of fit_fourier_hs()
nmc_default  <- formals(fit_fourier_hs)$nmc
burn_default <- formals(fit_fourier_hs)$burn
nmc  <- nmc_default
burn <- burn_default

args <- commandArgs(trailingOnly = TRUE)
for (a in grep("^--nmc=",  args, value = TRUE)) nmc  <- as.integer(sub("^--nmc=",  "", a))
for (a in grep("^--burn=", args, value = TRUE)) burn <- as.integer(sub("^--burn=", "", a))
run_names <- unlist(strsplit(grep("^--", args, value = TRUE, invert = TRUE), ","))
if (length(run_names) == 0) run_names <- apps$name

stopifnot("unknown application name" = all(run_names %in% apps$name),
          "nmc and burn must be positive integers" = !is.na(nmc) && nmc > 0 && !is.na(burn) && burn > 0)

# Section 4: a run with non-default MCMC length never overwrites the production outputs
quick   <- nmc != nmc_default || burn != burn_default
out_dir <- if (quick) file.path(root, "output", "_quick") else file.path(root, "output")
dir.create(out_dir, showWarnings = FALSE, recursive = TRUE)

cat(sprintf("root: %s\nrunning: %s   (nmc = %d, burn = %d)\nwriting to: %s\n",
            root, paste(run_names, collapse = ", "), nmc, burn, out_dir))

## ---------------------------------------------------------------------
## 2. Fit each series and write its outputs
## ---------------------------------------------------------------------
for (name in run_names) {
  dictionary <- apps$dictionary[apps$name == name]
  data_file  <- file.path(root, "data", paste0(name, ".csv"))

  dat <- read.csv(data_file, colClasses = c(t = "character"))
  stopifnot("data file needs columns t, x, y" = all(c("t", "x", "y") %in% names(dat)),
            "missing values in x or y" = !anyNA(dat$x) && !anyNA(dat$y),
            "x must lie in [0,1]" = all(dat$x >= 0 & dat$x <= 1))
  data_sha256 <- digest(file = data_file, algo = "sha256")   # hash of the file bytes

  cat(sprintf("\n== %s: n = %d, dictionary = %s\n", name, nrow(dat), dictionary))
  fit <- fit_fourier_hs(dat$x, dat$y, dictionary = dictionary, nmc = nmc, burn = burn)

  # --- <name>_fit.csv: t, x, y, fhat, lo, hi ---------------------------
  write.csv(data.frame(t = dat$t, x = dat$x, y = dat$y,
                       fhat = fit$fhat, lo = fit$lo, hi = fit$hi),
            file.path(out_dir, paste0(name, "_fit.csv")), row.names = FALSE)

  # --- <name>_summary.txt ----------------------------------------------
  summary_lines <- c(
    sprintf("application: %s", name),
    sprintf("run date: %s", format(Sys.time(), "%Y-%m-%d %H:%M %Z")),
    sprintf("n = %d", fit$n),
    sprintf("K = floor(n^0.7) = %d", fit$K),
    sprintf("dictionary = %s  %s", fit$dictionary,
            if (fit$dictionary == "cosine") "(M4): 1, cos(pi k x), k = 1..2K"
            else "(M2): 1, sin(2 pi k x), cos(2 pi k x), k = 1..K"),
    sprintf("columns = 2K+1 = %d", fit$p),
    sprintf("tau = K^-2 = %.6e", fit$tau),
    sprintf("nmc = %d, burn = %d, seed = %d", fit$nmc, fit$burn, fit$seed),
    sprintf("posterior mean of sigma = %.6f", fit$sigma),
    sprintf("active frequencies count = %d", length(fit$active)),
    sprintf("active frequencies = %s",
            if (length(fit$active) > 0) paste(fit$active, collapse = " ") else "none"),
    sprintf("run time (seconds) = %.1f", fit$seconds),
    sprintf("input data file = data/%s.csv", name),
    sprintf("input data sha256 = %s", data_sha256),
    sprintf("sampler: horseshoe %s, method.tau = fixed, method.sigma = Jeffreys",
            as.character(packageVersion("horseshoe")))
  )
  writeLines(summary_lines, file.path(out_dir, paste0(name, "_summary.txt")))
  cat(paste(summary_lines, collapse = "\n"), "\n")
}
