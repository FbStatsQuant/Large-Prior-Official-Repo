# check_linear_algebra.R: the structured linear algebra of hs_fast() against dense computations (paper, Appendix "Exact Gibbs
# sampling for fixed dictionaries", paragraph "Validation", items "Linear algebra" and "Coefficient draw").
#
# On six small designs (the five dictionary and design pairs of Table 3 and a cosine dictionary, n = 1500, J = 167):
#   (1) the Gram form that hs_fast() finds, against crossprod(X): largest entrywise error relative to max|X'X|, and largest error
#       on the correlation scale, |G_struct - X'X|_ij / sqrt(G_ii G_jj); the form must be the expected one;
#   (2) at a fixed state of the scales (w = 1 / (tau lambda)^2 after 200 sweeps), the posterior mean A^{-1} X'y and the Cholesky
#       factor L of A = X'X + diag(w), computed by the structured routines of the kernel, against solve() and chol();
#   pass rule for (1) and (2): every relative error <= 1e-10;
#   (3) the coefficient draw: 1e5 draws of theta ~ N(A^{-1} X'y, s2 A^{-1}) at that state, whitened with the dense Cholesky
#       factor (z = L'(theta - mu) / sigma), must look like independent N(0, 1) variables: the largest |mean| of a coordinate
#       (Bonferroni over the J coordinates at level 0.001), a Kolmogorov-Smirnov test of all pooled z (p-value > 0.001), the
#       Frobenius norm of (sample covariance - I) relative to its expectation sqrt(J (J + 1) / M) (<= 1.1), and the largest
#       entry of (sample covariance - I) in units of its standard deviation (Bonferroni over the J (J + 1) / 2 entries, 0.001).
# Usage (from this folder): Rscript check_linear_algebra.R [--quick]
#   --quick: n = 500 (J = 77) and 1e4 draws. Output: output/linear_algebra.csv. Exit status 0 if PASS, 1 if FAIL.
f <- sub("^--file=", "", grep("^--file=", commandArgs(FALSE), value = TRUE)[1])
HERE <- if (!is.na(f)) dirname(normalizePath(f)) else getwd()
source(file.path(HERE, "common.R"))

n <- if (QUICK) 500L else 1500L
M <- if (QUICK) 10000L else 100000L; CHUNK <- 10000L
TOL <- 1e-10
relmax <- function(a, b) max(abs(a - b)) / max(abs(b))
rows <- list()
add <- function(design, quantity, value, threshold, pass)
  rows[[length(rows) + 1]] <<- data.frame(design = design, quantity = quantity, value = value, threshold = threshold, pass = pass)

for (i in seq_len(nrow(DESIGNS))) {
  d <- small_design(i, n); X <- d$X; y <- d$y; p <- ncol(X); Xty <- drop(crossprod(X, y))
  cat(sprintf("\n%s, n = %d, J = %d\n", d$name, n, p))
  # (1) Gram form, through hs_fast()'s own setup code
  st <- suppressMessages(hsfast_structure(X, "auto")); G <- st$G
  add(d$name, sprintf("Gram form found = expected (%s)", d$form), NA_real_, NA_real_, st$kind == d$form)
  add(d$name, "Gram: max|G_struct - X'X| / max|X'X|", st$l0a, TOL, st$l0a <= TOL)
  add(d$name, "Gram: max|G_struct - X'X|_ij / sqrt(G_ii G_jj)", st$scaled, TOL, st$scaled <= TOL)
  # (2) a fixed state of the scales: 200 sweeps in package arithmetic from set.seed(99), half-Cauchy tau, Sigma2 = 0.01
  set.seed(99)
  s0 <- .hsfast$hsfast_kernel(X, y, Xty, n, st$gram, FALSE, 1, TRUE, 0.01, 200L, 50L, 7L, 50L, 50L, 0L)$state
  w <- 1 / (s0$tau * s0$lambda)^2; s2 <- s0$s2
  A <- G; diag(A) <- diag(A) + w; LA <- chol(A)                    # dense: A = LA' LA, LA upper triangular
  mu_dense <- solve(A, Xty, tol = 0)
  mu <- .hsfast$hsfast_fixed_draws(Xty, st$gram, w, s2, 0L)$mu
  L <- .hsfast$hsfast_dense_factor(st$gram, w)                     # lower triangular factor of the structured routines
  add(d$name, "posterior mean A^{-1} X'y: relative error vs solve()", relmax(mu, mu_dense), TOL, relmax(mu, mu_dense) <= TOL)
  add(d$name, "Cholesky factor of A: relative error vs chol()", relmax(L, t(LA)), TOL, relmax(L, t(LA)) <= TOL)
  # (3) M whitened draws of the coefficient block at that state
  mu_ch <- backsolve(LA, forwardsolve(t(LA), Xty))
  set.seed(101); S <- matrix(0, p, p); sz <- numeric(p); pool <- numeric(0); done <- 0L
  while (done < M) {
    m <- min(CHUNK, M - done); D <- .hsfast$hsfast_fixed_draws(Xty, st$gram, w, s2, m)$draws
    Z <- (LA %*% (D - mu_ch)) / sqrt(s2); sz <- sz + rowSums(Z); S <- S + tcrossprod(Z)
    pool <- c(pool, as.vector(Z)); done <- done + m
  }
  zmean <- sz / sqrt(M); zcrit <- qnorm(1 - 0.0005 / p); E <- S / M - diag(p)
  ks_p <- suppressWarnings(ks.test(pool, "pnorm")$p.value); rm(pool)
  frob <- sqrt(sum(E^2)) / sqrt(p * (p + 1) / M)
  ent <- max(abs(E) * sqrt(M / (1 + diag(p)))); ent_crit <- qnorm(1 - 0.0005 / (p * (p + 1) / 2))   # sd of an entry: 1/sqrt(M), diagonal sqrt(2/M)
  add(d$name, sprintf("draws: max_j |mean z_j| sqrt(M), M = %d", M), max(abs(zmean)), zcrit, max(abs(zmean)) <= zcrit)
  add(d$name, "draws: Kolmogorov-Smirnov p-value of pooled z (must exceed)", ks_p, 0.001, ks_p > 0.001)
  add(d$name, "draws: ||cov(z) - I||_F / sqrt(J(J+1)/M)", frob, 1.1, frob <= 1.1)
  add(d$name, "draws: max_ij |cov(z) - I|_ij / sd_ij", ent, ent_crit, ent <= ent_crit)
  tab <- do.call(rbind, rows); cur <- tab[tab$design == d$name, ]
  for (r in seq_len(nrow(cur))) cat(sprintf("  %-62s %10.3g  (threshold %8.3g)  %s\n", cur$quantity[r], cur$value[r], cur$threshold[r],
                                            if (cur$pass[r]) "ok" else "FAILED"))
}

tab <- do.call(rbind, rows)
write_out(tab, "linear_algebra.csv")
la <- grepl("relative error|Gram: max", tab$quantity)
cat(sprintf("\nlargest relative error of the linear algebra over the %d designs: %.2g (rule <= %g)\n", nrow(DESIGNS), max(tab$value[la]), TOL))
finish(all(tab$pass))
