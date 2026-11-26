# check_package_agreement.R: hs_fast(floor = "package") reproduces the R package horseshoe 0.2.0 draw for draw (paper, Appendix
# "Exact Gibbs sampling for fixed dictionaries", paragraph "Validation", item "Agreement with the package").
#
# On the six small designs of check_linear_algebra.R (n = 1500, J = 167), half-Cauchy global scale (start tau = 1) and fixed
# noise variance Sigma2 = 0.01, both samplers run 100 sweeps (burn = 0, nmc = 100) from set.seed(606). Compared:
#   theta: for every sweep s, max_j |theta_js - theta_js(package)| / max_j |theta_js(package)|;
#   tau and sigma^2: the relative difference of the two series, sweep by sweep;
#   the state of the random number generator (.Random.seed) after the 100 sweeps.
# Pass rule: every relative difference <= 1e-8 over the first 70 sweeps, and the final RNG states identical. The largest
# difference over all 100 sweeps is reported too: the two implementations round differently (the package solves with chol(A / s2)
# and its own order of operations), and in a slowly mixing chain such round-off differences can grow over the sweeps.
# Usage (from this folder): Rscript check_package_agreement.R [--quick]
#   --quick: n = 500 (J = 77). Output: output/package_agreement.csv. Exit status 0 if PASS, 1 if FAIL.
# Needs the package horseshoe, version 0.2.0 exactly (install.packages("horseshoe") gives it; other versions are not supported).
f <- sub("^--file=", "", grep("^--file=", commandArgs(FALSE), value = TRUE)[1])
HERE <- if (!is.na(f)) dirname(normalizePath(f)) else getwd()
if (!requireNamespace("horseshoe", quietly = TRUE) || as.character(utils::packageVersion("horseshoe")) != "0.2.0")
  stop("check_package_agreement.R needs the R package horseshoe, version 0.2.0 (found: ",
       if (requireNamespace("horseshoe", quietly = TRUE)) as.character(utils::packageVersion("horseshoe")) else "not installed", ")", call. = FALSE)
source(file.path(HERE, "common.R"))

n <- if (QUICK) 500L else 1500L
NS <- 100L; SEED <- 606L; TOL <- 1e-8; THROUGH <- 70L
relser <- function(a, b) abs(as.numeric(a) - as.numeric(b)) / pmax(abs(as.numeric(b)), .Machine$double.xmin)
rows <- list()
for (i in seq_len(nrow(DESIGNS))) {
  d <- small_design(i, n); X <- d$X; y <- d$y
  set.seed(SEED)
  invisible(capture.output(R0 <- horseshoe::horseshoe(y, X, method.tau = "halfCauchy", tau = 1, method.sigma = "fixed", Sigma2 = 0.01,
                                                      burn = 0, nmc = NS)))
  rng_ref <- .Random.seed
  set.seed(SEED)
  h <- suppressWarnings(suppressMessages(hs_fast(y, X, method.tau = "halfCauchy", tau = 1, method.sigma = "fixed", Sigma2 = 0.01,
                                                 burn = 0, nmc = NS, floor = "package")))
  rng_same <- identical(.Random.seed, rng_ref)
  B0 <- R0$BetaSamples
  rel_theta <- sapply(seq_len(NS), function(s) max(abs(h$BetaSamples[, s] - B0[, s])) / max(abs(B0[, s])))
  rel_tau <- relser(h$TauSamples, R0$TauSamples); rel_s2 <- relser(h$Sigma2Samples, R0$Sigma2Samples)
  m70 <- c(theta = max(rel_theta[1:THROUGH]), tau = max(rel_tau[1:THROUGH]), sigma2 = max(rel_s2[1:THROUGH]))
  m100 <- c(theta = max(rel_theta), tau = max(rel_tau), sigma2 = max(rel_s2))
  pass <- all(is.finite(c(rel_theta, rel_tau, rel_s2))) && all(m70 <= TOL) && rng_same
  rows[[i]] <- data.frame(design = d$name, n = n, J = d$J, gram_form = attr(h, "hsfast")$structure,
                          theta_max_rel_through_70 = m70[["theta"]], tau_max_rel_through_70 = m70[["tau"]],
                          sigma2_max_rel_through_70 = m70[["sigma2"]], theta_max_rel_all_100 = m100[["theta"]],
                          tau_max_rel_all_100 = m100[["tau"]], rng_state_identical = rng_same, pass = pass)
  cat(sprintf("%-21s %-7s  through sweep 70: theta %.2g, tau %.2g, sigma2 %.2g;  all 100: theta %.2g, tau %.2g;  RNG state identical: %s  %s\n",
              d$name, attr(h, "hsfast")$structure, m70[["theta"]], m70[["tau"]], m70[["sigma2"]], m100[["theta"]], m100[["tau"]],
              rng_same, if (pass) "ok" else "FAILED"))
}
tab <- do.call(rbind, rows)
write_out(tab, "package_agreement.csv")
cat(sprintf("largest relative difference over the first %d sweeps: %.2g (rule <= %g); RNG states identical: %d of %d\n", THROUGH,
            max(tab[, c("theta_max_rel_through_70", "tau_max_rel_through_70", "sigma2_max_rel_through_70")]), TOL,
            sum(tab$rng_state_identical), nrow(tab)))
finish(all(tab$pass))
