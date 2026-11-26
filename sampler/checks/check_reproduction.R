# check_reproduction.R: hs_fast(floor = "package") reproduces fits made earlier with the R package horseshoe 0.2.0 (paper,
# Appendix "Exact Gibbs sampling for fixed dictionaries", paragraph "Validation", item "Reproduction").
#
# The earlier fits: n = 20,000 equispaced points x = seq(0, 1, length.out = n), f0(x) = 0.5 |cos(pi x)|, y = f0 + N(0, 0.15^2);
# cosine dictionary 1, cos(pi k x), k = 1..1024 (1024 = floor(n^0.7) frequencies, 1025 columns); global scale fixed at
# tau = n^(-1.2), noise variance fixed at 0.15^2; burn = 2000, nmc = 5000. Data set s: set.seed(s), then y, then the fit with no
# reseed (the fit continues the random stream of the data). Their root mean squared errors, sqrt(mean((X BetaHat - f0)^2)) at the
# design points, are in ../reference_outputs/package_rmse_n20000.csv (seeds 1-100).
# This script refits the same data sets with hs_fast(floor = "package") and compares the RMSEs.
# Pass rule: relative difference <= 1e-6 for every seed run.
# Usage (from this folder): Rscript check_reproduction.R [--quick] [--seeds=K]
#   default: seeds 1-5 (about 20 seconds); --seeds=100: all 100 data sets (about 6 minutes), as in the paper; --quick: seed 1.
#   Output: output/reproduction.csv. Exit status 0 if PASS, 1 if FAIL.
f <- sub("^--file=", "", grep("^--file=", commandArgs(FALSE), value = TRUE)[1])
HERE <- if (!is.na(f)) dirname(normalizePath(f)) else getwd()
source(file.path(HERE, "common.R"))

nseeds <- as.integer(flag_value("seeds", if (QUICK) 1 else 5))
ref <- read.csv(file.path(HERE, "..", "reference_outputs", "package_rmse_n20000.csv"))
stopifnot(nseeds >= 1, nseeds <= nrow(ref), all(ref$seed == seq_len(nrow(ref))))
n <- 20000L; J <- floor(n^0.7); burn <- 2000L; nmc <- 5000L; sd_val <- 0.15
stopifnot(all(ref$n == n), all(ref$J == J))
x <- seq(0, 1, length.out = n)            # as in the earlier runs (not design_points(), which can differ in the last bit)
f0 <- 0.5 * abs(cos(pi * x))
X <- cosine_dictionary(x, J + 1)
tau <- 1 / (n^1.2)
rows <- vector("list", nseeds)
for (s in seq_len(nseeds)) {
  set.seed(s); y <- f0 + rnorm(n, mean = 0, sd = sd_val)
  h <- hs_fast(y, X, method.tau = "fixed", tau = tau, method.sigma = "fixed", Sigma2 = sd_val^2, burn = burn, nmc = nmc, floor = "package")
  r <- sqrt(mean((drop(X %*% h$BetaHat) - f0)^2))
  rows[[s]] <- data.frame(seed = s, n = n, J = J, gram_form = attr(h, "hsfast")$structure, rmse_hs_fast = r, rmse_package = ref$rmse[s],
                          rel_diff = abs(r - ref$rmse[s]) / ref$rmse[s])
  cat(sprintf("seed %3d  RMSE hs_fast %.15g  package %.15g  relative difference %.2g\n", s, r, ref$rmse[s], rows[[s]]$rel_diff)); flush.console()
}
tab <- do.call(rbind, rows)
write_out(tab, "reproduction.csv")
cat(sprintf("largest relative difference over %d seeds: %.2g (rule <= 1e-6)\n", nseeds, max(tab$rel_diff)))
finish(all(tab$rel_diff <= 1e-6))
