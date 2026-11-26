# hsfast.R: defines hs_fast(), an exact Gibbs sampler for the Horseshoe prior in the Gaussian linear model y = X theta + noise.
# Usage, from the repository root:
#   source("sampler/hsfast.R")      # compiles hs_fast.cpp on first use (cached in sampler/.cache/); needs Rcpp, RcppArmadillo, digest
#
# This code implements the Gibbs sampler of the R package 'horseshoe' (van der Pas, Scott, Chakraborty and Bhattacharya),
# version 0.2.0, with structured linear algebra for the draw of theta. It is distributed under GPL-3 (see sampler/LICENSE).
#
# hs_fast() takes the arguments of horseshoe::horseshoe() and returns the same list with one element appended, LambdaHat: the
# posterior mean of every lambda_k over the saved sweeps (the same sweeps that give BetaHat; horseshoe 0.2.0 has no such output).
# It has two extra arguments:
#   floor     = "exact" (default): the exact posterior; ALL the package's numerical floors are removed (lambda Fub >= 1e-4, tau
#               Fubt >= 1e-8, and under Jeffreys sigma the RSS and prior-term floors >= 1e-8) and the same slice draws are written in
#               stable form (expm1 / log1p, log-scale gamma CDF / quantile).
#               "package": horseshoe 0.2.0's arithmetic, floors included: the package's draws (to round-off) from the same set.seed(),
#               for the supported inputs (p <= n, burn and nmc multiples of thin).
#   structure = "auto" (default) | "diag" | "band" | "lowrank" | "dense" | a list(kind = ..., ...) giving the form of G = X'X.
# The Gibbs kernel (hs_fast.cpp) factors G + diag(1/(tau lambda)^2) using the form of G, so for a diagonal, banded or
# diagonal-plus-low-rank Gram the theta draw costs O(p) per sweep instead of O(p^3) (paper, Appendix "Exact Gibbs sampling for
# fixed dictionaries"). Every structured Gram is checked at setup against crossprod(X), and is used only if it passes all three checks:
#   (1) global:              max|G_struct - X'X| / max|X'X| <= 1e-10;
#   (2) entrywise on the correlation scale:  |G_struct - X'X|_ij <= 1e-10 sqrt(G_ii G_jj);
#   (3) relative to the precision:  ||G_struct - X'X||_F <= 1e-8 lambda_min(G_struct), or G_struct = X'X exactly.
# If no structured form passes, hs_fast() says so and uses the dense Gram. Dense: cond(X'X) > 1e10 is a warning; in exact mode the
# kernel checks the accuracy of every theta draw (backward error and mean-solve residual <= 1e-8) and stops otherwise.
# Names: in the code, check (1) is called "L0a" (HSFAST_L0A_TOL, .hsfast_l0a(), the l0a values and the L0a field of the result's
# "hsfast" attribute): the entrywise check of the structured Gram matrix against X'X. See sampler/README.md.

# Locate this file's folder (source() keeps the file name as 'ofile' in its own frame), so that hs_fast.cpp is found next to it.
# The environment variable HSFAST_DIR is only a fallback for when this file is not source()d by its path.
# Rcpp, RcppArmadillo and digest are loaded from the user's R library.
local({
  ofile <- NULL                                                                 # set by source() in its own frame
  for (i in rev(seq_len(sys.nframe()))) { f <- sys.frame(i)$ofile; if (is.character(f)) { ofile <- f; break } }
  dir <- if (!is.null(ofile)) dirname(normalizePath(ofile)) else Sys.getenv("HSFAST_DIR")
  if (!nzchar(dir) || !file.exists(file.path(dir, "hs_fast.cpp")))
    stop("hsfast.R: cannot locate hs_fast.cpp; source() this file by its path or set HSFAST_DIR", call. = FALSE)
  assign("HSFAST_DIR", dir, envir = globalenv())
})
.hsfast <- new.env()
local({
  # Compile cache keyed by the CONTENT hash of hs_fast.cpp: the kernel is copied to .cache/src/hs_fast_<sha256 prefix>.cpp and that
  # copy is compiled, so any change to hs_fast.cpp gives a new cache entry; file times play no part.
  src <- file.path(HSFAST_DIR, "hs_fast.cpp"); cache <- file.path(HSFAST_DIR, ".cache")
  h <- digest::digest(file = src, algo = "sha256")
  dir.create(file.path(cache, "src"), showWarnings = FALSE, recursive = TRUE)
  cp <- file.path(cache, "src", sprintf("hs_fast_%s.cpp", substr(h, 1, 16)))
  if (!file.exists(cp) || digest::digest(file = cp, algo = "sha256") != h) {
    tmp <- paste0(cp, ".", Sys.getpid()); file.copy(src, tmp, overwrite = TRUE); file.rename(tmp, cp) }
  if (digest::digest(file = cp, algo = "sha256") != h) stop("hsfast: kernel copy does not match its content hash: ", cp)
  Rcpp::sourceCpp(cp, cacheDir = cache, env = .hsfast)
  .hsfast$kernel_sha256 <- h
  .hsfast$wrapper_sha256 <- digest::digest(file = file.path(HSFAST_DIR, "hsfast.R"), algo = "sha256")
})
HSFAST_L0A_TOL <- 1e-10                      # tolerance of checks (1) and (2)

# ---------------------------------------------------------------- Gram structure
# Candidate exact forms of G = X'X (N = n - 1, x = seq(0, 1, length.out = n)):
#   cosine on the grid  (cols 1, cos(pi k x), k = 1..J):  G = diag(N, N/2, ..., N/2) + U U', U = [1, (-1)^k] / sqrt(2)   (rank 2)
#   real Fourier dictionary (1, sin 2 pi k x, cos 2 pi k x, ...):  G = diag(N, N/2, ...) + u u', u = 1 on constant and cosines (rank 1)
#   period-1 trig columns in any order: G = diag(G - x_n^2) + x_n x_n', x_n = last row of X (rank 1; "endpoint_rank1")
# Diagonal (Chebyshev at the Gauss-Chebyshev nodes, cosine at midpoints): d = diag(X'X), off-diagonal X'X is round-off.
# Banded (cubic B-spline): the band of X'X itself.  Anything else: dense X'X.
# .hsfast_dense_of(): the p x p matrix that a Gram form stands for (used by the checks).
.hsfast_dense_of <- function(gs) switch(gs$kind, lowrank = diag(gs$d, length(gs$d)) + gs$U %*% t(gs$U), diag = diag(gs$d, length(gs$d)),
  dense = gs$G, band = { p <- ncol(gs$Gb); G <- matrix(0, p, p)
    for (k in 0:gs$bw) for (j in 1:(p - k)) { G[j + k, j] <- gs$Gb[k + 1, j]; G[j, j + k] <- gs$Gb[k + 1, j] }; G })
.hsfast_lowrank_candidates <- function(n, p, X = NULL, G = NULL) {
  N <- n - 1; J <- p - 1; out <- list()
  if (p >= 2) out$cosine_grid <- list(kind = "lowrank", d = c(N, rep(N / 2, J)), U = cbind(rep(1, p), (-1)^(0:J)) / sqrt(2))
  if (p >= 2) { pairs <- (p - 1) %/% 2; u <- c(1, rep(c(0, 1), pairs)); if (length(u) < p) u <- c(u, 1)
    out$fourier_real <- list(kind = "lowrank", d = c(N, rep(N / 2, p - 1)), U = matrix(u, ncol = 1)) }
  # Period-1 trig columns in any order / scaling on x = seq(0, 1, n): rows 1..n-1 are a full periodic grid (orthogonal columns),
  # and row n repeats row 1, so G = diag(G - x_n^2) + x_n x_n'. Checked against X'X like every candidate.
  if (p >= 2 && !is.null(X) && !is.null(G)) { u <- X[n, ]; d <- diag(G) - u^2
    if (all(is.finite(d)) && all(d > 0)) out$endpoint_rank1 <- list(kind = "lowrank", d = d, U = matrix(u, ncol = 1)) }
  out
}
# Check (2), scale-aware: every entry on the correlation scale, |Gc - G|_ij <= tol sqrt(G_ii G_jj) (the diagonal
# entries give the relative diagonal error). Where G_ii G_jj = 0 the candidate must be exact. A global max|G| denominator alone can
# hide order-one errors in small columns.
.hsfast_scaled_err <- function(Gc, G) {
  s <- sqrt(pmax(diag(G), 0)); S <- tcrossprod(s); E <- abs(Gc - G)
  if (any(E[S == 0] != 0)) return(Inf)
  if (!any(S > 0)) return(0)
  max(E[S > 0] / S[S > 0])
}
.hsfast_band_of <- function(G, tol = 1e-12) {   # bandwidth of G at correlation-scale tolerance tol, and its lower band
  p <- ncol(G); s <- sqrt(pmax(diag(G), 0)); big <- abs(G) > tol * tcrossprod(s)
  bw <- if (any(big)) max(abs(row(G) - col(G))[big]) else 0L
  Gb <- matrix(0, bw + 1, p); for (k in 0:bw) Gb[k + 1, 1:(p - k)] <- G[cbind((1 + k):p, 1:(p - k))]
  list(kind = "band", Gb = Gb, bw = as.integer(bw))
}
# Check (3), precision-relative. The sampler factors Gc + D with D >= 0, so in EVERY sweep
#   ||P^{-1/2} (Gc - G) P^{-1/2}||_2 <= ||Gc - G||_F / lambda_min(Gc),   P = Gc + D,
# and a candidate is accepted only if Gc - G is exactly 0 or ||Gc - G||_F <= 1e-8 lambda_min(Gc). Lower bound used for lambda_min:
# diag and diag + low rank: min d (U U' >= 0); band / dense: the exact smallest eigenvalue for p <= 500, else 30 steps of inverse
# iteration with chol(Gc) from a fixed (non-random: the RNG stream is not touched) start, whose Rayleigh quotient (>= lambda_min)
# is divided by 2; a failed chol(Gc) gives 0 (reject unless exact).
HSFAST_PREC_TOL <- 1e-8
.hsfast_lmin_lb <- function(gs, Gc) {
  if (gs$kind %in% c("diag", "lowrank")) return(min(gs$d))
  p <- ncol(Gc)
  if (p <= 500) return(min(eigen(Gc, symmetric = TRUE, only.values = TRUE)$values))
  R <- tryCatch(chol(Gc), error = function(e) NULL); if (is.null(R)) return(0)
  v <- sin(1.2345 * seq_len(p)); v <- v / sqrt(sum(v^2))
  for (k in 1:30) { v <- backsolve(R, backsolve(R, v, transpose = TRUE)); v <- v / sqrt(sum(v^2)) }
  sum(v * drop(Gc %*% v)) / 2
}
# all three checks: (1) global (returned as l0a), (2) scale-aware, (3) precision-relative (prec = ||dG||_F / lambda_min lower bound;
# 0 if exact)
.hsfast_l0a <- function(gs, G) {
  Gc <- .hsfast_dense_of(gs); if (!all(is.finite(Gc))) return(c(l0a = Inf, scaled = Inf, prec = Inf))
  dG <- Gc - G; mG <- max(abs(G)); E <- max(abs(dG))
  prec <- if (all(dG == 0)) 0 else { lb <- .hsfast_lmin_lb(gs, Gc); if (lb > 0) sqrt(sum(dG^2)) / lb else Inf }
  c(l0a = if (mG > 0) E / mG else E, scaled = .hsfast_scaled_err(Gc, G), prec = prec)
}
# Manual / candidate structure lists: dimensions, finiteness and the factor preconditions (d >= 0 so that d + 1/(tau lambda)^2 > 0;
# band diagonal >= 0; dense symmetric). Errors, never NaN.
.hsfast_validate <- function(gs, p) {
  bad <- function(msg) stop("hs_fast: invalid structure list: ", msg, call. = FALSE)
  fin <- function(v) is.numeric(v) && length(v) > 0 && all(is.finite(v))
  if (!is.list(gs) || !is.character(gs$kind) || length(gs$kind) != 1 || !(gs$kind %in% c("diag", "band", "lowrank", "dense")))
    bad("kind must be one of \"diag\", \"band\", \"lowrank\", \"dense\"")
  if (gs$kind %in% c("diag", "lowrank")) {
    if (!(fin(gs$d) && is.null(dim(gs$d)) && length(gs$d) == p)) bad("d must be a finite numeric vector of length p = ncol(X)")
    if (any(gs$d < 0)) bad("d must be >= 0 (the factor needs d + 1/(tau lambda)^2 > 0)") }
  if (gs$kind == "lowrank" && !(is.matrix(gs$U) && fin(gs$U) && nrow(gs$U) == p && ncol(gs$U) >= 1)) bad("U must be a finite p x r matrix, r >= 1")
  if (gs$kind == "band") { bw <- gs$bw
    if (!(is.numeric(bw) && length(bw) == 1 && is.finite(bw) && bw == round(bw) && bw >= 0 && bw < p)) bad("bw must be a whole number in 0..p-1")
    if (!(is.matrix(gs$Gb) && fin(gs$Gb) && nrow(gs$Gb) == bw + 1 && ncol(gs$Gb) == p)) bad("Gb must be a finite (bw + 1) x p matrix")
    if (any(gs$Gb[1, ] < 0)) bad("the band's diagonal (Gb[1, ]) must be >= 0") }
  if (gs$kind == "dense" && !(is.matrix(gs$G) && fin(gs$G) && all(dim(gs$G) == p) && isSymmetric(unname(gs$G), tol = 0)))
    bad("G must be a finite symmetric p x p matrix")
  invisible(TRUE)
}
# Returns list(gs = Gram form, gram = kernel argument, kind, label, l0a, scaled, prec, G). The candidates are tried in the order
# diag, band, lowrank forms (or the user's list); the first one is used whose checks (1) and (2) are <= HSFAST_L0A_TOL and whose
# check (3) is <= HSFAST_PREC_TOL. Otherwise the dense Gram is used and a message says so (always, also in auto).
hsfast_structure <- function(X, structure = "auto", G = crossprod(X)) {
  n <- nrow(X); p <- ncol(X); tried <- character(0)
  if (!all(is.finite(G))) stop("hs_fast: crossprod(X) is not finite (overflow); rescale X", call. = FALSE)
  cand <- list()
  if (is.list(structure)) { .hsfast_validate(structure, p); cand$user <- structure }
  else {
    structure <- match.arg(structure, c("auto", "diag", "band", "lowrank", "dense"))
    if (structure %in% c("auto", "diag")) cand$diag <- list(kind = "diag", d = pmax(diag(G), 0))
    if (structure %in% c("auto", "band") && p >= 2) { b <- .hsfast_band_of(G)
      if (structure == "band" || (b$bw >= 1 && b$bw <= p / 8)) cand$band <- b }
    if (structure %in% c("auto", "lowrank")) cand <- c(cand, .hsfast_lowrank_candidates(n, p, X, G))
  }
  for (nm in names(cand)) { gs <- cand[[nm]]
    if (nm != "user" && !isTRUE(tryCatch(.hsfast_validate(gs, p), error = function(e) FALSE))) { tried <- c(tried, sprintf("%s (invalid form)", nm)); next }
    e <- .hsfast_l0a(gs, G)
    if (e[["l0a"]] <= HSFAST_L0A_TOL && e[["scaled"]] <= HSFAST_L0A_TOL && e[["prec"]] <= HSFAST_PREC_TOL)
      return(list(gs = gs, gram = .hsfast_gram_arg(gs), kind = gs$kind, label = nm, l0a = e[["l0a"]], scaled = e[["scaled"]], prec = e[["prec"]], G = G))
    tried <- c(tried, sprintf("%s (L0a %.1e, scaled %.1e, precision %.1e)", nm, e[["l0a"]], e[["scaled"]], e[["prec"]]))
  }
  if (!identical(structure, "dense"))
    message("hs_fast: no structured Gram form passed the checks (", if (length(tried)) paste(tried, collapse = ", ") else "none applicable",
            "; tolerances ", HSFAST_L0A_TOL, " entrywise, ", HSFAST_PREC_TOL, " precision-relative); using the dense Gram")
  gs <- list(kind = "dense", G = G)
  list(gs = gs, gram = .hsfast_gram_arg(gs), kind = "dense", label = "dense", l0a = 0, scaled = 0, prec = 0, G = G)
}
# The Gram argument of the kernel: type 0 = dense, 1 = diagonal, 2 = banded, 3 = diagonal + low rank.
.hsfast_gram_arg <- function(gs) switch(gs$kind, lowrank = list(type = 3L, d = gs$d, U = gs$U), diag = list(type = 1L, d = gs$d),
                                        band = list(type = 2L, Gb = gs$Gb, bw = gs$bw), dense = list(type = 0L, G = gs$G))

# ---------------------------------------------------------------- hs_fast
# Arguments as horseshoe::horseshoe() (method.tau "fixed" or "halfCauchy"; "truncatedCauchy" is not supported), plus floor and
# structure (see the top of this file). Returns the package's list plus LambdaHat; attr(result, "hsfast") records the Gram form
# used (structure = kind, structure_form = which candidate), the three check values, cond(X'X) for a dense Gram, the statistics of
# the dense accuracy check, the setup and sampler times, and the sha256 of the two source files.
hs_fast <- function(y, X, method.tau = c("fixed", "truncatedCauchy", "halfCauchy"), tau = 1,
                    method.sigma = c("fixed", "Jeffreys"), Sigma2 = 1,
                    burn = 1000, nmc = 5000, thin = 1, alpha = 0.05,
                    floor = c("exact", "package"), structure = "auto")
{
  method.tau <- match.arg(method.tau); method.sigma <- match.arg(method.sigma); floor <- match.arg(floor)
  if (method.tau == "truncatedCauchy")
    stop('hs_fast: method.tau = "truncatedCauchy" is not supported (the paper scripts and experiments use "fixed" and "halfCauchy"); ',
         'call horseshoe::horseshoe() for it', call. = FALSE)
  X <- as.matrix(X); if (!is.numeric(X)) stop("hs_fast: X must be a numeric matrix", call. = FALSE)
  y <- as.numeric(y); n <- nrow(X); p <- ncol(X)
  if (length(y) != n) stop("hs_fast: length(y) must equal nrow(X)", call. = FALSE)
  if (anyNA(X) || anyNA(y) || !all(is.finite(X)) || !all(is.finite(y))) stop("hs_fast: y and X must be finite (no NA)", call. = FALSE)
  if (floor == "package" && p > n)
    stop('hs_fast: floor = "package" reproduces horseshoe 0.2.0 only for p <= n (for p > n the package switches to another ',
         'algorithm with a different random stream); use floor = "exact"', call. = FALSE)
  isint <- function(v) length(v) == 1 && is.finite(v) && v == round(v)
  if (!isint(burn) || burn < 0 || !isint(nmc) || nmc < 1 || !isint(thin) || thin < 1)
    stop("hs_fast: burn >= 0, nmc >= 1 and thin >= 1 must be whole numbers", call. = FALSE)
  if (nmc %% thin != 0 || burn %% thin != 0)
    stop("hs_fast: burn and nmc must be multiples of thin (the package's sample indexing is ill-defined otherwise)", call. = FALSE)
  if (method.tau == "fixed" || method.tau == "halfCauchy") if (!(length(tau) == 1 && is.finite(tau) && tau > 0))
    stop("hs_fast: tau must be one positive number (it is also the starting value under halfCauchy)", call. = FALSE)
  if (!(length(Sigma2) == 1 && is.finite(Sigma2) && Sigma2 > 0)) stop("hs_fast: Sigma2 must be one positive number", call. = FALSE)
  if (!(length(alpha) == 1 && alpha > 0 && alpha < 1)) stop("hs_fast: alpha must be in (0, 1)", call. = FALSE)
  burn <- as.integer(burn); nmc <- as.integer(nmc); thin <- as.integer(thin)

  ## setup: Gram structure (the three checks, dense fallback), X'y
  t_setup <- proc.time()[["elapsed"]]
  st <- hsfast_structure(X, structure)
  Xty <- drop(crossprod(X, y))
  ## dense Gram: cond(G) estimate (1 / rcond(chol(G))^2, LAPACK dtrcon; Inf if chol(G) fails). A large value is a WARNING only:
  ## the prior regularizes G + D; in exact mode the per-sweep accuracy check in the kernel decides (stops if inaccurate).
  condG <- NA_real_
  if (st$kind == "dense") { R <- tryCatch(chol(st$G), error = function(e) NULL)
    condG <- if (is.null(R)) Inf else 1 / rcond(R, triangular = TRUE)^2
    if (condG > 1e10) warning(sprintf("hs_fast: the design is numerically collinear (cond(X'X) ~ %.1e > 1e10). %s Chebyshev nodes (or orthogonalized columns) avoid this.",
                                      condG, if (floor == "exact") "Exact mode checks the accuracy of every theta draw and stops if the prior is lost to rounding." else
                                        "Package mode does not check it (horseshoe 0.2.0 has the same limitation)."), call. = FALSE) }
  t_setup <- proc.time()[["elapsed"]] - t_setup

  ## Gibbs sampler: all post-burn sweeps i with i %% thin == 0 are kept (the package's rule; nbatch = 1, max_save = nmc / thin).
  ## clamp 7 = the package's lambda, tau and sigma^2 floors; 0 = none. Jeffreys RSS is computed from the residual y - X theta.
  ## guard 1 (exact mode): the kernel's per-sweep accuracy check of the dense theta draw (read-only; stops above 1e-8).
  ## Kernel arguments after the prior settings: burn, nmc, clamp, nbatch = 1, max_save = effsamp, full = 0, guard.
  effsamp <- nmc %/% thin
  o <- .hsfast$hsfast_kernel(X, y, Xty, n, st$gram, method.tau == "fixed", tau, method.sigma == "fixed", Sigma2,
                             burn, nmc, if (floor == "package") 7L else 0L, 1L, effsamp, 0L, if (floor == "exact") 1L else 0L)
  gd <- o$guard; gstat <- function(v, f) if (length(v)) f(v) else NA_real_
  betaout <- o$draws; tauout <- as.numeric(o$tau); sigmaSqout <- as.numeric(o$s2)
  stopifnot(ncol(betaout) == effsamp, o$thin == thin, length(o$lambda_mean) == ncol(X))
  if (!all(is.finite(betaout)) || !all(is.finite(tauout)) || !all(is.finite(sigmaSqout)))
    stop("hs_fast: the chain produced non-finite values (theta, tau or Sigma2); check the inputs and the prior settings", call. = FALSE)

  ## posterior summaries: taken from the R package 'horseshoe' 0.2.0 (GPL-3), file R/horseshoe.R, lines 251-268.
  ## The last list element, LambdaHat, is added here (it is not in the package).
  pMean=apply(betaout,1,mean)
  pMedian=apply(betaout,1,stats::median)
  pSigma=mean(sigmaSqout)
  pTau=mean(tauout)
  left <- base::floor(alpha*effsamp/2)
  right <- ceiling((1-alpha/2)*effsamp)
  BetaSort <- apply(betaout, 1, sort, decreasing = F)
  left.points <- BetaSort[left, ]
  right.points <- BetaSort[right, ]
  result=list("BetaHat"=pMean, "LeftCI" = left.points,
              "RightCI" = right.points,"BetaMedian"=pMedian,
              "Sigma2Hat"=pSigma,"TauHat"=pTau,"BetaSamples"=betaout,
              "TauSamples" = tauout, "Sigma2Samples" = sigmaSqout,
              "LambdaHat" = as.numeric(o$lambda_mean))              # mean of lambda over the saved sweeps (not in the package)
  attr(result, "hsfast") <- list(floor = floor, structure = st$kind, structure_form = st$label, L0a = st$l0a, scaled_err = st$scaled,
                                 precision_err = st$prec, cond_G = condG,
                                 guard = list(on = isTRUE(gd$on), max_r = gstat(gd$r, max), median_r = gstat(gd$r, stats::median),
                                              max_r_w = gstat(gd$r_w, max), median_r_w = gstat(gd$r_w, stats::median),
                                              max_r_mean = gstat(gd$r_mean, max), median_r_mean = gstat(gd$r_mean, stats::median)),
                                 setup_seconds = t_setup, sampler_seconds = o$seconds, kernel_sha256 = .hsfast$kernel_sha256,
                                 wrapper_sha256 = .hsfast$wrapper_sha256)
  result
}
