# =====================================================================
# Series dictionaries + fixed-scale horseshoe: functions only.
# Implements METHODS_SPEC.md (version 3), Section 1, equations (M1)-(M4).
#
#   (M1)  y_i = f(x_i) + e_i,  e_i iid N(0, sigma^2),  x_i in [0,1]
#   (M2)  Fourier: f(x) = beta_0 + sum_{k=1}^K [beta_{k,s} sin(2 pi k x) + beta_{k,c} cos(2 pi k x)]
#   (M4)  cosine:  f(x) = beta_0 + sum_{k=1}^{2K} beta_k cos(pi k x)
#         both with K = floor(n^b), b = 0.7, and 2K+1 columns
#   (M3)  beta_j | lambda_j, sigma ~ N(0, sigma^2 tau^2 lambda_j^2), lambda_j ~ C+(0,1),
#         j = 1..2K+1 (constant included), tau = K^-2 fixed, p(sigma^2) ∝ 1/sigma^2
#
# Used by run_applications.R. Requires the 'horseshoe' package (0.2.0).
# =====================================================================

library(horseshoe)

## ---------------------------------------------------------------------
## (M2) Fourier dictionary xi(x): 2K+1 columns
##      column 1 = 1, column 2k = sin(2 pi k x), column 2k+1 = cos(2 pi k x)
## ---------------------------------------------------------------------
fourier_basis <- function(x, K) {
  X <- matrix(1, length(x), 2 * K + 1)
  for (k in 1:K) {
    X[, 2 * k]     <- sin(2 * pi * k * x)
    X[, 2 * k + 1] <- cos(2 * pi * k * x)
  }
  X
}

## ---------------------------------------------------------------------
## (M4) cosine dictionary xi(x): 2K+1 columns
##      column 1 = 1, column k+1 = cos(pi k x), k = 1..2K
## ---------------------------------------------------------------------
cosine_basis <- function(x, K) {
  X <- matrix(1, length(x), 2 * K + 1)
  for (k in 1:(2 * K)) {
    X[, k + 1] <- cos(pi * k * x)
  }
  X
}

## ---------------------------------------------------------------------
## Design matrix for the chosen dictionary: "fourier" (M2) or "cosine" (M4)
## ---------------------------------------------------------------------
dictionary_basis <- function(x, K, dictionary) {
  if (dictionary == "fourier") fourier_basis(x, K) else cosine_basis(x, K)
}

## ---------------------------------------------------------------------
## (M2), (M4) number of frequencies, K = floor(n^b)
## ---------------------------------------------------------------------
number_of_frequencies <- function(n, b) {
  floor(n^b)
}

## ---------------------------------------------------------------------
## (M3) fixed global scale, tau = K^-2
## ---------------------------------------------------------------------
global_scale <- function(K) {
  K^(-2)
}

## ---------------------------------------------------------------------
## (M1), (M3) posterior sampling with the 'horseshoe' package:
##   method.tau = "fixed" (tau = K^-2), method.sigma = "Jeffreys",
##   single chain, set.seed(seed) immediately before the call.
##   Returns BetaSamples (p x nmc), BetaHat, LeftCI, RightCI, Sigma2Samples, ...
## ---------------------------------------------------------------------
sample_posterior <- function(y, X, tau, nmc, burn, seed) {
  set.seed(seed)
  horseshoe(y, X, method.tau = "fixed", tau = tau,
            method.sigma = "Jeffreys", burn = burn, nmc = nmc)
}

## ---------------------------------------------------------------------
## Posterior summaries of f (Section 1):
##   fhat(x) = xi(x)^T E[beta | y]                     (posterior mean curve)
##   lo, hi  = 2.5% and 97.5% quantiles over m of xi(x)^T beta^(m)
##   Xeval holds xi(x) at the evaluation points, one row per point.
## ---------------------------------------------------------------------
posterior_curve <- function(Xeval, hs) {
  fhat  <- drop(Xeval %*% hs$BetaHat)
  fdraw <- Xeval %*% hs$BetaSamples          # row i, column m: xi(x_i)^T beta^(m)
  band  <- apply(fdraw, 1, quantile, probs = c(0.025, 0.975))
  list(fhat = fhat, lo = band[1, ], hi = band[2, ])
}

## ---------------------------------------------------------------------
## Active frequencies (Section 1, descriptive only), from the package's
## marginal 95% credible intervals (LeftCI/RightCI):
##   (M2) Fourier: k in 1..K is active if the interval of beta_{k,s}
##        (column 2k) or of beta_{k,c} (column 2k+1) excludes 0;
##   (M4) cosine:  k in 1..2K is active if the interval of beta_k
##        (column k+1) excludes 0.
## ---------------------------------------------------------------------
active_frequencies <- function(hs, K, dictionary) {
  excludes0 <- hs$LeftCI > 0 | hs$RightCI < 0
  if (dictionary == "fourier") {
    k <- 1:K
    k[excludes0[2 * k] | excludes0[2 * k + 1]]
  } else {
    k <- 1:(2 * K)
    k[excludes0[k + 1]]
  }
}

## ---------------------------------------------------------------------
## Posterior mean of sigma, E[sigma | y] = mean over m of sqrt(sigma^2 (m))
## ---------------------------------------------------------------------
posterior_mean_sigma <- function(hs) {
  mean(sqrt(hs$Sigma2Samples))
}

## ---------------------------------------------------------------------
## Full fit (M1)-(M4) for one series, on its n original points.
##   x, y       : observations, x in [0,1]
##   dictionary : "fourier" (M2) or "cosine" (M4)
## Returns fhat, lo, hi at x, K, tau, posterior mean of sigma, the active
## frequencies, and the elapsed time (seconds) of the whole fit (design,
## sampling, summaries).
## ---------------------------------------------------------------------
fit_fourier_hs <- function(x, y, dictionary = c("fourier", "cosine"), b = 0.7,
                           nmc = 20000, burn = 10000, seed = 20261027) {
  dictionary <- match.arg(dictionary)
  t0 <- proc.time()[["elapsed"]]
  n  <- length(y)

  K   <- number_of_frequencies(n, b)                   # (M2)/(M4)
  tau <- global_scale(K)                               # (M3)
  X   <- dictionary_basis(x, K, dictionary)            # (M2) or (M4), 2K+1 columns
  hs  <- sample_posterior(y, X, tau, nmc, burn, seed)  # (M1), (M3)

  curve <- posterior_curve(X, hs)                      # evaluated at the observed x

  list(fhat       = curve$fhat,
       lo         = curve$lo,
       hi         = curve$hi,
       n          = n,
       K          = K,
       p          = ncol(X),
       tau        = tau,
       dictionary = dictionary,
       sigma      = posterior_mean_sigma(hs),
       active     = active_frequencies(hs, K, dictionary),
       nmc        = nmc,
       burn       = burn,
       seed       = seed,
       seconds    = proc.time()[["elapsed"]] - t0)
}
