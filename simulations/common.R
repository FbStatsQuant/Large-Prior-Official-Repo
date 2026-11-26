# common.R: shared code of the simulation studies (paper Sections 3.1-3.3). Scripts in simulations/recovery/, benchmarks/ and
# scaling/ load it with  source("../common.R")  (or by any path); it then loads ../sampler/hsfast.R and ../sampler/dictionaries.R.
# Contents: the target functions f1 and f2 and their noise levels, the J rule, the four (function, dictionary, design) pairs of
# the paper, the data of one pair at one n, the Horseshoe fit with its summaries and MCMC diagnostics, and the figure style.

# Locate this file's folder (source() keeps the file name as 'ofile' in its own frame), then load the sampler and the dictionaries.
local({
  ofile <- NULL
  for (i in rev(seq_len(sys.nframe()))) { f <- sys.frame(i)$ofile; if (is.character(f)) { ofile <- f; break } }
  sim_dir <- if (!is.null(ofile)) dirname(normalizePath(ofile)) else getwd()
  if (!file.exists(file.path(sim_dir, "common.R"))) stop("common.R: source() this file by its path, e.g. source(\"../common.R\")", call. = FALSE)
  sampler_dir <- normalizePath(file.path(sim_dir, "..", "sampler"), mustWork = TRUE)
  source(file.path(sampler_dir, "hsfast.R"))
  source(file.path(sampler_dir, "dictionaries.R"))
})

# ---------------------------------------------------------------- settings of the simulation studies
f_fun <- list(
  f1 = function(x) 0.5 * abs(sin(pi * (x - 0.5))),         # = 0.5 |cos(pi x)|; smoothness alpha = 1
  f2 = function(x) abs(sin(1.3 * pi * (x - 0.35)))^3)      # smoothness alpha = 3
SIGMA  <- c(f1 = 0.15, f2 = 0.20)                         # noise standard deviation; the fits use the true noise variance
ALPHA  <- c(f1 = 1, f2 = 3)
N_GRID <- as.integer(seq(1000, 20000, by = 500))          # the 39 sample sizes of Section 3.3
GRID_M <- 2000L                                           # RMSE on the uniform grid u_m = (m - 1/2) / M, m = 1..M
FPTS_X <- c(0.1, 0.3, 0.5, 0.7, 0.9)                      # fitted-value traces at the design points nearest these x
NBATCH <- 50L                                             # batch-means MCSE with 50 batches

# ---- J rule: J = floor(n^0.7) columns in total (intercept included), computed in INTEGER arithmetic as the largest J with
# J^10 <= n^7, so that no rounding of n^0.7 can move J.
.big_pow <- function(a, e) {                    # little-endian base-1e6 limbs of a^e, a a whole number <= 1e9
  limbs <- 1
  for (i in seq_len(e)) {
    carry <- 0
    for (k in seq_along(limbs)) { v <- limbs[k] * a + carry; limbs[k] <- v %% 1e6; carry <- v %/% 1e6 }
    while (carry > 0) { limbs <- c(limbs, carry %% 1e6); carry <- carry %/% 1e6 }
  }
  limbs
}
.big_le <- function(A, B) {
  if (length(A) != length(B)) return(length(A) < length(B))
  for (k in rev(seq_along(A))) if (A[k] != B[k]) return(A[k] < B[k])
  TRUE
}
J_of_n <- function(n) {
  n <- as.integer(n); stopifnot(length(n) == 1L, n >= 2L)
  rhs <- .big_pow(n, 7L); J <- as.integer(floor(n^0.7))
  while (J > 1L && !.big_le(.big_pow(J, 10L), rhs)) J <- J - 1L
  while (.big_le(.big_pow(J + 1L, 10L), rhs)) J <- J + 1L
  J
}

# ---- the four (function, dictionary, design) pairs of Sections 3.2-3.3. expect = the Gram form hs_fast() must find.
CELLS <- data.frame(
  id     = c("f1_fourier", "f1_bspline", "f2_chebyshev", "f2_bspline"),
  fun    = c("f1", "f1", "f2", "f2"),
  basis  = c("fourier", "bspline", "chebyshev", "bspline"),
  design = c("equispaced", "equispaced", "chebyshev_nodes", "chebyshev_nodes"),
  expect = c("lowrank", "band", "diag", "band"),
  stringsAsFactors = FALSE)
CELLS$sigma <- unname(SIGMA[CELLS$fun])

# Everything one pair needs at one n: design points x, design matrix X, data y = f(x) + sigma z, the truth f0 = f(x), the uniform
# grid u with f(u) and the dictionary on it (Bu). z is the standard-normal vector of this n, shared by all pairs
# (set.seed(data seed); z <- rnorm(n)).
build_cell <- function(cell, n, J, z) {
  x <- design_points(cell$design, n)
  X <- dictionary_matrix(cell$basis, x, J)
  stopifnot(nrow(X) == n, ncol(X) == J)
  f <- f_fun[[cell$fun]]
  f0 <- f(x); y <- f0 + cell$sigma * z
  u <- (seq_len(GRID_M) - 0.5) / GRID_M
  list(x = x, X = X, y = y, f0 = f0, u = u, f_u = f(u), Bu = dictionary_matrix(cell$basis, u, J))
}

# ---------------------------------------------------------------- MCMC diagnostics (base R + stats)
# Effective sample size of a scalar series: Geyer's initial monotone positive sequence on the autocorrelation function.
ess_geyer <- function(x) {
  x <- as.numeric(x); N <- length(x)
  if (N < 8L || !all(is.finite(x))) return(NA_real_)
  if (var(x) == 0) return(NA_real_)
  L <- min(N - 1L, 10000L)
  rho <- stats::acf(x, lag.max = L, type = "correlation", plot = FALSE)$acf[, 1, 1]      # rho[1] = lag 0
  m <- (length(rho) %/% 2L)
  G <- rho[2L * seq_len(m) - 1L] + rho[2L * seq_len(m)]                                     # Gamma_k = rho_2k + rho_2k+1, k = 0..
  K <- which(G <= 0)[1L]; if (is.na(K)) K <- m + 1L
  G <- G[seq_len(K - 1L)]
  if (length(G) > 1L) for (k in 2:length(G)) G[k] <- min(G[k], G[k - 1L])                   # monotone
  tau_int <- -1 + 2 * sum(G)
  if (!is.finite(tau_int) || tau_int < 1e-12) tau_int <- 1e-12
  N / tau_int
}

# Split R-hat (Gelman et al. BDA3; Stan): `chains` is a list of equal-length numeric vectors (1 or 2 chains); each is split in two halves.
split_rhat <- function(chains) {
  S <- do.call(cbind, lapply(chains, function(ch) { h <- length(ch) %/% 2L; cbind(ch[seq_len(h)], ch[h + seq_len(h)]) }))   # h x (2 m)
  h <- nrow(S); W <- mean(apply(S, 2, var)); B <- h * var(colMeans(S))
  if (!is.finite(W) || W <= 0) return(NA_real_)
  sqrt(((h - 1) / h * W + B / h) / W)
}

# Batch-means MCSE of the posterior-mean fitted vector X theta_hat. `Bs` is p x nmc (rows = coefficients). The mean is linear, so the
# batch means of X theta equal X times the batch means of theta; this never forms the n x nmc matrix.
batch_mcse_fitted <- function(X, Bs, nbatch) {
  nmc <- ncol(Bs); bs <- nmc %/% nbatch; stopifnot(bs * nbatch == nmc)
  bm <- vapply(seq_len(nbatch), function(b) rowMeans(Bs[, ((b - 1L) * bs + 1L):(b * bs), drop = FALSE]), numeric(nrow(Bs)))   # p x nbatch
  FB <- X %*% bm                                                                                                     # n x nbatch
  sqrt(apply(FB, 1, var) / nbatch)                                                                                   # MCSE_i
}

# ---------------------------------------------------------------- one Horseshoe fit
# The fit of Sections 3.2-3.3: half-Cauchy prior on tau (start 1), sigma^2 fixed at the true noise variance, burn 2000, 5000 saved
# sweeps, floor = "exact", Gram form found by hs_fast(). set.seed(mcmc_seed) immediately before the call. `b` is build_cell()'s list.
# Stops if hs_fast() does not find the expected Gram form (for "lowrank" a rank-one form: fourier_real or endpoint_rank1).
# Returns one flat list: errors, sparsity counts, tau_hat, the coefficient summaries, the MCMC diagnostics, timings, the Gram form.
fit_horseshoe <- function(cell, n, J, b, mcmc_seed, burn = 2000L, nmc = 5000L) {
  X <- b$X; y <- b$y
  set.seed(mcmc_seed)
  t0 <- proc.time()[["elapsed"]]
  fit <- hs_fast(y, X, method.tau = "halfCauchy", tau = 1, method.sigma = "fixed", Sigma2 = cell$sigma^2,
                 burn = burn, nmc = nmc, thin = 1L, alpha = 0.05, floor = "exact", structure = "auto")
  t_fit <- proc.time()[["elapsed"]] - t0
  att <- attr(fit, "hsfast")

  ok_struct <- identical(att$structure, cell$expect) &&
    (cell$expect != "lowrank" || att$structure_form %in% c("fourier_real", "endpoint_rank1"))     # both are rank 1
  if (!ok_struct) stop(sprintf("%s n=%d: expected Gram form '%s', hs_fast selected '%s' (%s)", cell$id, n,
                               cell$expect, att$structure, att$structure_form), call. = FALSE)

  # errors at the design points (posterior mean and median) and on the uniform grid
  th <- fit$BetaHat; thm <- fit$BetaMedian
  fh <- drop(X %*% th); fhm <- drop(X %*% thm)
  rmse_design <- sqrt(mean((fh - b$f0)^2)); rmse_design_med <- sqrt(mean((fhm - b$f0)^2))
  rmse_grid <- sqrt(mean((drop(b$Bu %*% th) - b$f_u)^2)); rmse_grid_med <- sqrt(mean((drop(b$Bu %*% thm) - b$f_u)^2))
  # sparsity counts: |theta_hat_k| > 1/J; the same with the robust threshold max(1/J, sigma sqrt(2 log J / n) / ||xi_k||_n);
  # and the number of 95% equal-tail credible intervals that exclude 0
  colrms <- sqrt(colMeans(X^2))
  thr_rob <- pmax(1 / J, cell$sigma * sqrt(2 * log(J) / n) / colrms)
  idx_q <- which(abs(th) > 1 / J); idx_qrob <- which(abs(th) > thr_rob); qhat <- length(idx_q); qrob <- length(idx_qrob)
  th_sd <- apply(fit$BetaSamples, 1, stats::sd); th_lo <- as.numeric(fit$LeftCI); th_hi <- as.numeric(fit$RightCI)
  lam_hat <- as.numeric(fit$LambdaHat)
  idx_ci <- which(th_lo > 0 | th_hi < 0); qci <- length(idx_ci)

  # diagnostics: ESS of log tau and of the fitted values at five design points, single-chain split R-hat, batch-means MCSE
  logtau <- log(fit$TauSamples)
  fidx <- vapply(FPTS_X, function(x0) which.min(abs(b$x - x0)), integer(1))
  ftr <- X[fidx, , drop = FALSE] %*% fit$BetaSamples                                         # 5 x nmc traces of f-hat at the design points
  mcse_i <- batch_mcse_fitted(X, fit$BetaSamples, NBATCH)
  mcse_rms <- sqrt(mean(mcse_i^2))
  ess_logtau <- ess_geyer(logtau)
  ess_f <- apply(ftr, 1, ess_geyer)
  rhat1_f <- apply(ftr, 1, function(v) split_rhat(list(v))); rhat1_logtau <- split_rhat(list(logtau))

  list(cell = cell$id, n = n, J = J, mcmc_seed = mcmc_seed,
       rmse_design = rmse_design, rmse_design_median = rmse_design_med, rmse_grid = rmse_grid, rmse_grid_median = rmse_grid_med,
       qhat = qhat, qhat_rob = qrob, qhat_ci = qci, tau_hat = fit$TauHat,
       beta_hat = th, beta_sd = th_sd, beta_ci_left = th_lo, beta_ci_right = th_hi, lambda_hat = lam_hat,
       mcse_rel = mcse_rms / rmse_design, mcse_rms = mcse_rms, ess_logtau = ess_logtau, ess_fpts = ess_f,
       rhat1_f = rhat1_f, rhat1_logtau = rhat1_logtau,
       hs_fast_wall = t_fit, setup_s = att$setup_seconds, sampler_s = att$sampler_seconds,
       structure = att$structure, structure_form = att$structure_form)
}

# ---------------------------------------------------------------- figure style (base graphics)
COL <- list(grid = "#E6E6E6", axis = "#4D4D4D", lab = "#222222", truth = "#1A1A1A", hs = "#2457A6", alt = "#D17A22")
mns <- function(v, d = 3) sub("^-", "−", formatC(v, format = "f", digits = d))      # typographic minus
panel <- function(xlim, ylim, xat, yat, xlab_at = xat, ylab_at = yat, xlabels = xlab_at, ylabels = ylab_at, xlab = "", ylab = "", log = "") {
  plot.new(); plot.window(xlim, ylim, log = log)
  abline(v = xat, h = yat, col = COL$grid, lwd = 0.7)
  axis(1, at = xlab_at, labels = xlabels, lwd = 0, col.axis = COL$axis, cex.axis = 0.85, line = -0.7)
  axis(2, at = ylab_at, labels = ylabels, lwd = 0, col.axis = COL$axis, cex.axis = 0.85, las = 1, line = -0.7)
  if (nzchar(xlab)) mtext(xlab, side = 1, line = 1.6, col = COL$lab, cex = 0.9)
  if (nzchar(ylab)) mtext(ylab, side = 2, line = 2.6, col = COL$lab, cex = 0.9)
}
# Draw a figure twice: vector PDF (cairo) and 300-dpi PNG, as dir/stem.pdf and dir/stem.png; w, h in inches.
save_figure <- function(stem, w, h, draw, dir) {
  if (!isTRUE(capabilities("cairo")))
    stop("save_figure: this R build has no cairo support (needed for the vector PDF with UTF-8 glyphs and the 300-dpi PNG)", call. = FALSE)
  dir.create(dir, showWarnings = FALSE, recursive = TRUE)
  grDevices::cairo_pdf(file.path(dir, paste0(stem, ".pdf")), width = w, height = h, family = "sans"); draw(); dev.off()
  png(file.path(dir, paste0(stem, ".png")), width = round(w * 300), height = round(h * 300), res = 300, type = "cairo", family = "sans"); draw(); dev.off()
  invisible(file.path(dir, paste0(stem, c(".pdf", ".png"))))
}

# Folder of the running script (from Rscript's --file= argument), else the working directory.
script_dir <- function() {
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd()
}
