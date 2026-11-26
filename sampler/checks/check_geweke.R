# check_geweke.R: joint-distribution tests in the sense of Geweke (2004) of the exact mode of hs_fast() (floor = "exact"), with two
# deliberately introduced errors that the tests must detect (paper, Appendix "Exact Gibbs sampling for fixed dictionaries",
# paragraph "Validation", item "Joint-distribution tests").
#
# The test (restart form): draw (lambda, tau, sigma^2, theta) from the prior and y from the model, compute test functions h,
# apply one update block of the sampler (or full sweeps), and compute h again. A correct block leaves the joint distribution of
# parameters and data invariant, so every difference d = h1 - h0 has mean zero; z = mean(d) / (sd(d) / sqrt(M)) over M independent
# replicates is approximately N(0, 1). The blocks are the sampler's own C++ functions: geweke_driver.cpp is compiled together with
# the text of ../hs_fast.cpp. Test functions per coefficient k: atan(theta_k / s_k) and its square, log lambda_k and its square, and
# two products; then log tau, log sigma^2, their squares and products (6 J + 6 in all; geweke_driver.cpp lists them).
# Design: cosine dictionary 1, cos(pi k x), k = 1..7, on 40 equispaced points (J = 8; X'X is diagonal plus rank two, so the
# structured factorization is the one under test). Priors: half-Cauchy global scale with
#   random_sigma: sigma^2 ~ IG(5, 1.25) (a proper prior, run through the sampler's Jeffreys update with 10 pseudo-observations);
#   fixed_sigma : sigma^2 = 0.25.
# Cases: the sigma^2, tau and full-sweep blocks (and 5 full sweeps) under random_sigma; the tau block and the full sweep under
# fixed_sigma; and three cases with an introduced error, made on a COPY of the text of hs_fast.cpp (the shipped file is not changed):
#   local_scale_error : the truncation point of the local-scale slice draw is halved (exp. CDF at ub/2 instead of ub);
#   global_scale_error: the shape of the global-scale gamma draw is J/2 instead of (J + 1)/2.
# Decision: cutoff = qnorm(1 - 0.01 / (2 N)), N = number of test functions over the clean cases (Bonferroni, family-wise 1%).
# A clean case passes if max|z| <= cutoff, at most 1e-5 M replicates were non-finite, and every test function the block cannot move
# is exactly unchanged; a case with an introduced error passes (is detected) if max|z| > cutoff.
# Usage (from this folder): Rscript check_geweke.R [--quick] [--M_clean=1e6] [--M_bug=2e5]
#   The default is the paper's run: M = 1e6 replicates per clean case (5e5 for the 5-sweep case), 2e5 per error case, seeds
#   7401-7409 (about 1.5 minutes, plus about 1 minute to compile three versions of the kernel on first use, cached in output/cache/).
#   --quick: M = 1e5 and 2e4. Output: output/geweke.csv. Exit status 0 if PASS, 1 if FAIL.
f <- sub("^--file=", "", grep("^--file=", commandArgs(FALSE), value = TRUE)[1])
HERE <- if (!is.na(f)) dirname(normalizePath(f)) else getwd()
source(file.path(HERE, "common.R"))

M_CLEAN <- as.integer(flag_value("M_clean", if (QUICK) 1e5 else 1e6))
M_BUG <- as.integer(flag_value("M_bug", if (QUICK) 2e4 else 2e5))

# the sampler's text, and two copies with an introduced error (each substitution must match exactly one line)
ktxt <- readLines(file.path(HERE, "..", "hs_fast.cpp")); dtxt <- readLines(file.path(HERE, "geweke_driver.cpp"))
patch <- function(txt, old, new) { i <- grep(old, txt, fixed = TRUE); stopifnot(length(i) == 1); txt[i] <- sub(old, new, txt[i], fixed = TRUE); txt }
variants <- list(clean = ktxt,
  local_scale_error = patch(ktxt, "else Fub[j] = -std::expm1(-tempps[j] * ub[j]);", "else Fub[j] = -std::expm1(-0.5 * tempps[j] * ub[j]);"),
  global_scale_error = patch(ktxt, "shape = (p + 1) / 2.0", "shape = (p + 0) / 2.0"))
cache <- file.path(OUT, "cache"); dir.create(cache, showWarnings = FALSE)
cat("compiling the sampler with the test driver (three versions; cached in output/cache/) ...\n"); flush.console()
envs <- lapply(variants, function(tx) { e <- new.env(); Rcpp::sourceCpp(code = paste(c(tx, dtxt), collapse = "\n"), cacheDir = cache, env = e); e })

x <- seq(0, 1, length.out = 40); X <- cosine_dictionary(x, 8)
st <- hsfast_structure(X, "auto"); stopifnot(st$kind == "lowrank")
PRI <- list(random_sigma = list(tfix = FALSE, tau = 1, sfix = FALSE, s2 = 1, m0 = 10L, S0 = 2.5),     # tau ~ C+(0,1), sigma^2 ~ IG(5, 1.25)
            fixed_sigma = list(tfix = FALSE, tau = 1, sfix = TRUE, s2 = 0.25, m0 = 0L, S0 = 0))      # tau ~ C+(0,1), sigma^2 = 0.25
BLK <- c(full = 0L, theta = 1L, lambda = 2L, tau = 3L, s2 = 4L)
cases <- list(); add <- function(...) cases[[length(cases) + 1]] <<- data.frame(..., stringsAsFactors = FALSE)
for (b in c("s2", "tau", "full")) add(prior = "random_sigma", block = b, nsweep = 1L, variant = "clean", role = "clean", M = M_CLEAN)
add(prior = "random_sigma", block = "full", nsweep = 5L, variant = "clean", role = "clean", M = M_CLEAN %/% 2L)
for (b in c("tau", "full")) add(prior = "fixed_sigma", block = b, nsweep = 1L, variant = "clean", role = "clean", M = M_CLEAN)
add(prior = "random_sigma", block = "full", nsweep = 1L, variant = "local_scale_error", role = "introduced error", M = M_BUG)
add(prior = "random_sigma", block = "full", nsweep = 1L, variant = "global_scale_error", role = "introduced error", M = M_BUG)
add(prior = "fixed_sigma", block = "full", nsweep = 1L, variant = "global_scale_error", role = "introduced error", M = M_BUG)
cases <- do.call(rbind, cases); cases$seed <- 7400L + seq_len(nrow(cases))

# Which test functions a block can move: a, a2, a_c depend on theta and sigma; a2_l on theta, sigma, lambda; l, l2 on lambda;
# lt, lt2 on tau; ls, ls2 on sigma; lt_ls on tau, sigma; lt_mean_l on tau, lambda (and is 0 if log tau = 0).
# A movable function must give a finite z with sd > 0; any other must be exactly unchanged (sd 0, mean 0).
DEP <- list(a = c("theta", "s"), a2 = c("theta", "s"), l = "lambda", l2 = "lambda", a_c = c("theta", "s"), a2_l = c("theta", "s", "lambda"),
            lt = "tau", lt2 = "tau", ls = "s", ls2 = "s", lt_ls = c("tau", "s"), lt_mean_l = c("tau", "lambda"))
p <- ncol(X)
fn <- c(paste0(rep(c("a", "a2", "l", "l2", "a_c", "a2_l"), p), "_", rep(1:p, each = 6)), "lt", "lt2", "ls", "ls2", "lt_ls", "lt_mean_l")
active_fns <- function(block, pr) {
  moved <- switch(block, theta = "theta", lambda = "lambda", tau = if (!pr$tfix) "tau", s2 = if (!pr$sfix) "s",
                  full = c("theta", "lambda", if (!pr$tfix) "tau", if (!pr$sfix) "s"))
  base <- sub("_[0-9]+$", "", fn); act <- vapply(base, function(b) any(DEP[[b]] %in% moved), TRUE)
  zero <- base %in% c("lt_ls", "lt_mean_l") & pr$tfix & log(pr$tau) == 0 & !("tau" %in% moved)    # product with log tau = 0
  act & !zero
}
res <- vector("list", nrow(cases))
for (i in seq_len(nrow(cases))) {
  cs <- cases[i, ]; pr <- PRI[[cs$prior]]
  set.seed(cs$seed); t0 <- proc.time()[["elapsed"]]
  o <- envs[[cs$variant]]$gw_restart(st$gram, X, BLK[[cs$block]], cs$M, pr$tfix, pr$tau, pr$sfix, pr$s2, pr$m0, pr$S0, 0L, cs$nsweep)
  md <- as.numeric(o$mean_d); sdd <- as.numeric(o$sd_d); act <- active_fns(cs$block, pr)
  z <- md / (sdd / sqrt(o$M)); z[!act] <- NA
  pattern_ok <- all(is.finite(z[act]) & sdd[act] > 0) && all(sdd[!act] == 0 & md[!act] == 0)
  res[[i]] <- data.frame(K = sum(act), pattern_ok = pattern_ok, max_abs_z = max(abs(z), na.rm = TRUE), worst = fn[which.max(abs(z))],
                         nonfinite = o$nonfinite, seconds = round(proc.time()[["elapsed"]] - t0, 1))
  cat(sprintf("[%d] %-12s %-4s x%d  %-18s  M %7d  K %2d  max|z| %7.2f (%s)\n", i, cs$prior, cs$block, cs$nsweep, cs$variant, cs$M,
              res[[i]]$K, res[[i]]$max_abs_z, res[[i]]$worst)); flush.console()
}
cases <- cbind(cases, do.call(rbind, res))
N_clean <- sum(cases$K[cases$role == "clean"]); cut <- qnorm(1 - 0.01 / (2 * N_clean)); cases$cutoff <- cut
cases$pass <- ifelse(cases$role == "clean", cases$max_abs_z <= cut & cases$nonfinite <= 1e-5 * cases$M & cases$pattern_ok,
                     cases$max_abs_z > cut)
write_out(cases, "geweke.csv")
clean <- cases$role == "clean"
cat(sprintf("cutoff %.2f (N = %d test functions over the clean cases, family-wise 1%%)\n", cut, N_clean))
cat(sprintf("clean cases: largest |z| %.2f; %d of %d pass\n", max(cases$max_abs_z[clean]), sum(cases$pass[clean]), sum(clean)))
cat(sprintf("introduced errors: smallest |z| %.2f; %d of %d detected\n", min(cases$max_abs_z[!clean]), sum(cases$pass[!clean]), sum(!clean)))
finish(all(cases$pass))
