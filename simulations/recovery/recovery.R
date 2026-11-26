# recovery.R: coefficient recovery with an approximately sparse truth (paper Section 3.1, Figure 1).
# Chebyshev dictionary, n = 2000 Gauss-Chebyshev nodes, J = 1000 columns: twenty large coefficients, then 0.001 for the other 980.
# One simulated data set; Horseshoe (hs_fast, structured exact sampler) and ordinary least squares on the same data.
#   Rscript recovery.R            paper settings; writes results/
#   Rscript recovery.R --quick    n = 400, J = 200, 200 burn-in and 500 saved sweeps; writes quick_results/
#   --out=DIR                     write to DIR instead
# Outputs: coefficients.csv (one row per coefficient) and summary.txt (every number quoted in Section 3.1). Figure 1 is drawn
# from coefficients.csv by make_figure.R.
options(warn = 1)
here <- local({ a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
                if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd() })
source(file.path(here, "..", "common.R"))

args  <- commandArgs(trailingOnly = TRUE)
quick <- "--quick" %in% args
out   <- sub("^--out=", "", grep("^--out=", args, value = TRUE))
out   <- if (length(out) == 1L) out else file.path(here, if (quick) "quick_results" else "results")
dir.create(out, showWarnings = FALSE, recursive = TRUE)

# ---- settings
n <- if (quick) 400L else 2000L
J <- if (quick) 200L else 1000L
SIGMA6 <- 0.2; TAIL6 <- 0.001
BURN <- if (quick) 200L else 2000L
NMC  <- if (quick) 500L else 5000L
THETA_BIG <- c(1.2, 2.1, 0.8, 1.5, 2.4, 0.6, 1.9, 1.1, 2.3, 0.9, 1.7, 0.5, 2.0, 1.4, 0.7, 2.5, 1.0, 1.8, 1.3, 1.6)   # printed in the paper
DATA_SEED <- 1L; MCMC_SEED <- 1001L; ALPHA6 <- 0.05
stopifnot(length(THETA_BIG) == 20L, all(THETA_BIG >= 0.5 & THETA_BIG <= 2.5), !anyDuplicated(THETA_BIG))

# ---- design, truth, data
x <- design_points("chebyshev_nodes", n); X <- chebyshev_dictionary(x, J)
G <- crossprod(X); gram_dev <- max(abs(G - diag(n, J))) / n                 # X'X = n I at the nodes (J + J - 2 < 2n)
if (gram_dev > 1e-10) stop(sprintf("X'X is not n I to round-off (max rel dev %.2e)", gram_dev))
theta0 <- c(THETA_BIG, rep(TAIL6, J - 20L)); f0 <- drop(X %*% theta0)
set.seed(DATA_SEED); z <- rnorm(n); y <- f0 + SIGMA6 * z
big <- 1:20; tail <- 21:J

# ---- OLS (QR): known-sigma (z) intervals
qx <- qr(X); if (qx$rank != J) stop("OLS design rank deficient")
b_ols <- qr.coef(qx, y); se_ols <- SIGMA6 * sqrt(diag(chol2inv(qr.R(qx))))
zq <- qnorm(1 - ALPHA6 / 2); lo_ols <- b_ols - zq * se_ols; hi_ols <- b_ols + zq * se_ols
# ---- OLS: classical t-intervals, s^2 = RSS / (n - J), df = n - J
df <- n - J; s2 <- sum((y - drop(X %*% b_ols))^2) / df
se_t <- sqrt(s2 * diag(chol2inv(qr.R(qx)))); tq <- qt(0.975, df)
lo_t <- b_ols - tq * se_t; hi_t <- b_ols + tq * se_t

# ---- Horseshoe (hs_fast)
set.seed(MCMC_SEED); t0 <- proc.time()[["elapsed"]]
fit <- hs_fast(y, X, method.tau = "halfCauchy", tau = 1, method.sigma = "fixed", Sigma2 = SIGMA6^2, burn = BURN, nmc = NMC, thin = 1L,
               alpha = ALPHA6, floor = "exact", structure = "auto")
t_hs <- proc.time()[["elapsed"]] - t0; ah <- attr(fit, "hsfast")
if (!identical(ah$structure, "diag")) stop("hs_fast did not use the diagonal Gram (got ", ah$structure, ")")
B <- fit$BetaSamples; if (!identical(dim(B), c(J, NMC))) stop("BetaSamples has the wrong shape")
post_sd <- apply(B, 1L, sd)
ess_big <- vapply(big, function(k) ess_geyer(B[k, ]), 0)
ess_logtau <- ess_geyer(log(fit$TauSamples))
bmeans <- sapply(seq_len(NBATCH), function(b) rowMeans(B[, ((b - 1L) * (NMC / NBATCH) + 1L):(b * (NMC / NBATCH)), drop = FALSE]))   # J x NBATCH
mcse_bm <- apply(bmeans, 1L, sd) / sqrt(NBATCH); ess_bm <- (post_sd / mcse_bm)^2                    # batch-means ESS, every theta_k
rm(B); invisible(gc())

hs_mean <- fit$BetaHat; lo_hs <- fit$LeftCI; hi_hs <- fit$RightCI
covered <- function(lo, hi, v) lo <= v & v <= hi
l2 <- function(v) sqrt(sum(v^2))
mse_des <- function(b) mean((drop(X %*% b) - f0)^2)

# identity check: X'X = n I  =>  mean((X(b - theta0))^2) = ||b - theta0||^2 (to round-off)
mse_hs <- mse_des(hs_mean); mse_ols <- mse_des(b_ols)
id_dev <- abs(c(mse_hs, mse_ols) - c(l2(hs_mean - theta0)^2, l2(b_ols - theta0)^2)) / c(mse_hs, mse_ols)
if (any(id_dev > 1e-8)) stop("design MSE != squared l2 coefficient error (X'X = n I identity failed)")

# ---- coefficients.csv
coef_all <- data.frame(k = seq_len(J), theta0 = theta0, hs_mean = hs_mean, hs_median = fit$BetaMedian, hs_sd = post_sd,
                       hs_lo95 = lo_hs, hs_hi95 = hi_hs, hs_ess = ess_bm, lambda_hat = fit$LambdaHat,
                       ols = b_ols, ols_se_t = se_t, ols_lo95_t = lo_t, ols_hi95_t = hi_t, ols_lo95_z = lo_ols, ols_hi95_z = hi_ols)
write.csv(coef_all, file.path(out, "coefficients.csv"), row.names = FALSE)

# ---- summary.txt
c_hs <- covered(lo_hs, hi_hs, theta0); c_t <- covered(lo_t, hi_t, theta0); c_z <- covered(lo_ols, hi_ols, theta0)
z_hs <- covered(lo_hs, hi_hs, 0); z_t <- covered(lo_t, hi_t, 0); z_z <- covered(lo_ols, hi_ols, 0)
wd <- function(lo, hi, i) mean((hi - lo)[i])
two <- function(label, a, b, fmt = "%.6g") sprintf("%-58s Horseshoe %-12s OLS %s", paste0(label, ":"), sprintf(fmt, a), sprintf(fmt, b))
si <- capture.output(print(sessionInfo())); si <- si[!grepl("^(BLAS|LAPACK)", si)]      # drop library paths
txt <- c(
  "Coefficient recovery (paper Section 3.1, Figure 1)", "",
  "Settings",
  sprintf("  dictionary: Chebyshev, J = %d columns (first column 1, then sqrt(2) T_k(2x - 1)); design: n = %d Gauss-Chebyshev nodes", J, n),
  sprintf("  truth: theta0[1:20] = %s; theta0[21:%d] = %g", paste(THETA_BIG, collapse = ", "), J, TAIL6),
  sprintf("  noise sd sigma = %.2f (known to the sampler); y = X theta0 + sigma z, z = {set.seed(%d); rnorm(n)}", SIGMA6, DATA_SEED),
  sprintf("  Horseshoe: half-Cauchy scale, tau start 1, sigma fixed, %d burn-in and %d saved sweeps, floor exact, structure auto; set.seed(%d) just before hs_fast()", BURN, NMC, MCMC_SEED),
  "  OLS: QR; classical t-intervals with s^2 = RSS/(n - J), df = n - J; known-sigma z-intervals for reference",
  sprintf("  mode: %s", if (quick) "quick (reduced sizes: the numbers are not those of the paper)" else "paper settings"),
  sprintf("  Gram form found by hs_fast: %s", ah$structure),
  sprintf("  Gram check max|X'X - nI|/n: %.3g", gram_dev),
  sprintf("  OLS t-interval variance estimate s^2 = %.6f (s = %.5f), df = %d, t quantile %.5f", s2, sqrt(s2), df, tq),
  sprintf("  noise sd of one OLS coefficient, sigma/sqrt(n): %.5f", SIGMA6 / sqrt(n)), "",
  "Errors (l2 norms of the coefficient error; on this design the squared l2 error over all coefficients equals the design-point MSE)",
  two("l2 error, twenty large coefficients", l2((hs_mean - theta0)[big]), l2((b_ols - theta0)[big])),
  two("l2 error, tail (k = 21..J)", l2((hs_mean - theta0)[tail]), l2((b_ols - theta0)[tail])),
  two("l2 error, all coefficients", l2(hs_mean - theta0), l2(b_ols - theta0)),
  two("design-point MSE x 1e3", 1000 * mse_hs, 1000 * mse_ols), "",
  "Tail estimates",
  two("max |estimate| over the tail", max(abs(hs_mean[tail])), max(abs(b_ols[tail]))),
  two("mean |estimate| over the tail", mean(abs(hs_mean[tail])), mean(abs(b_ols[tail]))), "",
  "95% intervals (Horseshoe: equal-tailed credible intervals; OLS: t-intervals)",
  two("intervals containing the truth, twenty large", sum(c_hs[big]), sum(c_t[big]), "%d"),
  two("intervals containing the truth, tail", sum(c_hs[tail]), sum(c_t[tail]), "%d"),
  two("tail intervals containing zero", sum(z_hs[tail]), sum(z_t[tail]), "%d"),
  two("mean interval width, twenty large", wd(lo_hs, hi_hs, big), wd(lo_t, hi_t, big)),
  two("mean interval width, tail", wd(lo_hs, hi_hs, tail), wd(lo_t, hi_t, tail)),
  sprintf("  number of tail coefficients: %d", length(tail)),
  sprintf("  OLS known-sigma z-intervals: containing the truth, twenty large %d, tail %d; tail intervals containing zero %d; mean width %.6g",
          sum(c_z[big]), sum(c_z[tail]), sum(z_z[tail]), wd(lo_ols, hi_ols, big)), "",
  "Sampler",
  sprintf("  minimum effective sample size over the twenty large coefficients: %.0f", min(ess_big)),
  sprintf("  minimum batch-means effective sample size over all coefficients: %.0f", min(ess_bm)),
  sprintf("  effective sample size of log(tau): %.0f", ess_logtau),
  sprintf("  posterior mean of tau (tau_hat): %.5g", fit$TauHat),
  sprintf("  sampler seconds (setup and %d sweeps): %.1f", BURN + NMC, t_hs), "",
  "R session", si)
writeLines(txt, file.path(out, "summary.txt"))
cat(txt[seq_len(which(txt == "R session") - 1L)], sep = "\n")
cat(sprintf("\nWrote %s/\n", basename(out)))
