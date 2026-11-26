# timing.R: Table 3 of the paper (Appendix "Exact Gibbs sampling for fixed dictionaries", table "tab:timing"): seconds for 1000
# sweeps of hs_fast() at n = 20,000 and J = floor(n^0.7) = 1024, on one core, for five dictionary and design pairs:
#   Fourier on the equispaced design (Gram matrix diagonal + rank one), Chebyshev at the Gauss-Chebyshev nodes (diagonal),
#   Chebyshev on the equispaced design (dense), cubic B-splines on each design (banded).
# Data: f0(x) = sin(4 pi x) exp(-2x), y = f0 + N(0, 0.1^2), set.seed(20261125). Prior and chain: half-Cauchy global scale
# (start tau = 1), noise variance fixed at its true value 0.01, burn = 0, nmc = 1000, floor = "exact", structure = "auto";
# set.seed(1) before each fit. Building X is not timed.
# Reported per design: the Gram form found, the setup seconds (X'X, the structure checks, X'y; for a dense Gram also the estimate
# of cond(X'X)), the sampler seconds (the 1000 sweeps), and the wall seconds of the whole call (setup, sweeps, posterior summaries).
#
# The dense design is reported twice. In exact mode hs_fast() checks, in every sweep, the accuracy of the dense coefficient draw
# (backward error of the factorization and residual of the mean solve; this adds O(J^2) operations per sweep). The paper's row was
# timed without that check, and its caption gives the whole call with the check on (59.5 s). So this script times
#   "on" : hs_fast() as it is, with the check;
#   "off": the same 1000 sweeps with the check off, by calling the compiled kernel directly with the arguments hs_fast() passes
#          except the last one (the check switch) set to 0; setup and posterior summaries are timed as hs_fast() does them.
# The check only reads the state of the chain, so both rows give identical draws (the script verifies this).
#
# Usage (from this folder): Rscript timing.R [--quick]
#   about 2 minutes, most of it the two dense rows; --quick: n = 2000 (J = 204) and 200 sweeps, a few seconds.
#   Output: output/timing.csv (output/timing_quick.csv with --quick) and the printed table. The paper's numbers are in
#   reference_outputs/timing_paper.csv; timings depend on the machine and its load.
f <- sub("^--file=", "", grep("^--file=", commandArgs(FALSE), value = TRUE)[1])
HERE <- if (!is.na(f)) dirname(normalizePath(f)) else getwd()
source(file.path(HERE, "hsfast.R")); source(file.path(HERE, "dictionaries.R"))
OUT <- file.path(HERE, "output"); dir.create(OUT, showWarnings = FALSE)
QUICK <- "--quick" %in% commandArgs(TRUE)

n <- if (QUICK) 2000L else 20000L; J <- as.integer(floor(n^0.7)); NSW <- if (QUICK) 200L else 1000L
DESIGNS <- data.frame(
  dictionary = c("Fourier", "Chebyshev", "Chebyshev", "B-spline", "B-spline"),
  basis      = c("fourier", "chebyshev", "chebyshev", "bspline", "bspline"),
  design     = c("equispaced", "chebyshev_nodes", "equispaced", "equispaced", "chebyshev_nodes"),
  expected   = c("lowrank", "diag", "dense", "band", "band"), stringsAsFactors = FALSE)
FORM <- c(lowrank = "diagonal + rank one", diag = "diagonal", dense = "dense", band = "banded")
DESIGN_LABEL <- c(equispaced = "equispaced grid", chebyshev_nodes = "Gauss-Chebyshev nodes")

# hs_fast() with its warning about collinear designs recorded instead of printed (the dense design is numerically collinear)
fit <- function(y, X) {
  warn <- character(0)
  h <- withCallingHandlers(suppressMessages(hs_fast(y, X, method.tau = "halfCauchy", tau = 1, method.sigma = "fixed", Sigma2 = 0.01,
                                                    burn = 0, nmc = NSW, floor = "exact", structure = "auto")),
                           warning = function(w) { warn <<- c(warn, conditionMessage(w)); invokeRestart("muffleWarning") })
  list(h = h, warn = warn)
}
# The same sweeps with the accuracy check off: hs_fast()'s setup, kernel call and posterior summaries, timed the same way.
fit_check_off <- function(y, X) {
  t_setup <- proc.time()[["elapsed"]]
  st <- suppressMessages(hsfast_structure(X, "auto"))
  Xty <- drop(crossprod(X, y))
  condG <- NA_real_
  if (st$kind == "dense") { R <- tryCatch(chol(st$G), error = function(e) NULL)
    condG <- if (is.null(R)) Inf else 1 / rcond(R, triangular = TRUE)^2 }
  t_setup <- proc.time()[["elapsed"]] - t_setup
  # arguments as in hs_fast(): tau not fixed, start 1; sigma fixed at 0.01; burn, nmc; floor "exact" (0); nbatch 1; save all;
  # full 0; last argument = accuracy check, here 0 (off)
  o <- .hsfast$hsfast_kernel(X, y, Xty, nrow(X), st$gram, FALSE, 1, TRUE, 0.01, 0L, NSW, 0L, 1L, NSW, 0L, 0L)
  betaout <- o$draws; tauout <- as.numeric(o$tau); alpha <- 0.05; effsamp <- NSW
  pMean <- apply(betaout, 1, mean); pMedian <- apply(betaout, 1, stats::median)        # the summaries of hs_fast()
  left <- floor(alpha * effsamp / 2); right <- ceiling((1 - alpha / 2) * effsamp)
  BetaSort <- apply(betaout, 1, sort, decreasing = FALSE); left.points <- BetaSort[left, ]; right.points <- BetaSort[right, ]
  list(kind = st$kind, setup = t_setup, sampler = o$seconds, tau = tauout, beta = betaout, guard_on = isTRUE(o$guard$on))
}

rows <- list(); same_draws <- NA
for (i in seq_len(nrow(DESIGNS))) {
  d <- DESIGNS[i, ]
  x <- design_points(d$design, n); X <- dictionary_matrix(d$basis, x, J)
  set.seed(20261125L); f0 <- sin(4 * pi * x) * exp(-2 * x); y <- f0 + rnorm(n, 0, 0.1)
  set.seed(1); t0 <- proc.time()[["elapsed"]]
  r <- fit(y, X)
  wall <- proc.time()[["elapsed"]] - t0; a <- attr(r$h, "hsfast")
  if (a$structure != d$expected) stop(sprintf("timing.R: %s on the %s design: Gram form %s, expected %s", d$dictionary, d$design, a$structure, d$expected))
  if (!all(is.finite(r$h$BetaSamples)) || !all(is.finite(r$h$TauSamples))) stop("timing.R: non-finite draws")
  make_row <- function(check, setup, sampler, wall) data.frame(dictionary = d$dictionary, design = DESIGN_LABEL[[d$design]], n = n, J = J,
    sweeps = NSW, gram_form = FORM[[a$structure]], accuracy_check = check, setup_s = round(setup, 3), sampler_s = round(sampler, 3),
    wall_s = round(wall, 3), stringsAsFactors = FALSE)
  if (a$structure == "dense") {
    if (length(r$warn)) cat("note: hs_fast() warned that this design is numerically collinear (cond(X'X) > 1e10); expected here\n")
    set.seed(1); t0 <- proc.time()[["elapsed"]]
    k <- fit_check_off(y, X)
    wall_off <- proc.time()[["elapsed"]] - t0
    stopifnot(k$kind == "dense", !k$guard_on)
    same_draws <- identical(k$tau, r$h$TauSamples) && identical(k$beta, r$h$BetaSamples)
    rows[[length(rows) + 1]] <- make_row("off", k$setup, k$sampler, wall_off)
    rows[[length(rows) + 1]] <- make_row("on", a$setup_seconds, a$sampler_seconds, wall)
    rm(k)
  } else rows[[length(rows) + 1]] <- make_row("not applicable", a$setup_seconds, a$sampler_seconds, wall)
  for (cur in rows[(length(rows) - (a$structure == "dense")):length(rows)])
    cat(sprintf("%-9s %-21s %-19s check %-14s setup %6.2f s  sampler %7.2f s  wall %7.2f s\n", d$dictionary, cur$design, cur$gram_form,
                cur$accuracy_check, cur$setup_s, cur$sampler_s, cur$wall_s))
  flush.console()
  rm(X, r); invisible(gc(verbose = FALSE))
}
tab <- do.call(rbind, rows)
if (!isTRUE(same_draws)) stop("timing.R: the dense fit with the accuracy check off did not give the same draws as with it on")
out <- file.path(OUT, if (QUICK) "timing_quick.csv" else "timing.csv")
write.csv(tab, out, row.names = FALSE)
cat(sprintf("\nSeconds for %d sweeps at n = %d, J = %d (one core). Dense design: the accuracy check is off in the row the paper\n", NSW, n, J))
cat("reports and on in hs_fast() as it is; both rows gave identical draws.\n\n")
options(width = 150)
print(tab[, c("dictionary", "design", "gram_form", "accuracy_check", "setup_s", "sampler_s", "wall_s")], row.names = FALSE)
cat("\nwrote", file.path("output", basename(out)), "\n")
