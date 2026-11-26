# worker.R: one task of the scaling experiment (paper Section 3.3, Table 2 and Figure 3).
# One task = one data set s and one (target, dictionary) pair, fitted at every sample size of the grid in increasing order.
#
#   Rscript worker.R T                 T = 1, ..., 400; writes results/task_TTT.csv (one row per n)
#   Rscript worker.R T --n=1000,1500   only these sample sizes (values of the grid, increasing)
#   Rscript worker.R T --burn=B --nmc=M --out=DIR
#   Rscript worker.R T --quick         same as --n=1000,1500 --burn=200 --nmc=500, written to quick_results/
# Relative folders (--out) are taken relative to this script's folder.
#
# Task map: data set s = (T - 1) %/% 4 + 1, pair = CELLS$id[(T - 1) %% 4 + 1] (f1_fourier, f1_bspline, f2_chebyshev, f2_bspline),
# so tasks 1-4 are data set 1 and tasks 397-400 data set 100. Seeds: for every n, set.seed(s); z <- rnorm(n) gives the noise
# (the same z for both targets and both dictionaries, so the two dictionaries of a target see the same data), and
# set.seed(1000 + s) is called immediately before every sampler call (inside fit_horseshoe()).
# The output file is written atomically (temporary file, then rename) and an existing file is never overwritten.

options(warn = 1)
here <- local({
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd()
})
in_here <- function(p) if (grepl("^(/|~|[A-Za-z]:)", p)) p else file.path(here, p)   # relative folders: next to this script
source(file.path(here, "..", "common.R"))        # loads ../../sampler/hsfast.R (compiled on first use) and the dictionaries

# ---- arguments
args <- commandArgs(trailingOnly = TRUE)
opt <- function(name, default) {
  h <- grep(paste0("^--", name, "="), args, value = TRUE)
  if (length(h)) sub(paste0("^--", name, "="), "", h[length(h)]) else default
}
known <- "^--(n|burn|nmc|out)=|^--quick$"
pos <- args[!grepl("^--", args)]
if (length(pos) != 1L || !grepl("^[0-9]+$", pos) || any(grepl("^--", args) & !grepl(known, args)))
  stop("usage: Rscript worker.R T [--n=1000,1500] [--burn=2000] [--nmc=5000] [--out=DIR] [--quick]", call. = FALSE)
task <- as.integer(pos)
ntask <- 4L * 100L
if (task < 1L || task > ntask) stop(sprintf("task must be 1..%d", ntask), call. = FALSE)
quick <- "--quick" %in% args
ns   <- as.integer(strsplit(opt("n", if (quick) "1000,1500" else paste(N_GRID, collapse = ",")), ",", fixed = TRUE)[[1]])
burn <- as.integer(opt("burn", if (quick) "200" else "2000"))
nmc  <- as.integer(opt("nmc", if (quick) "500" else "5000"))
out_dir <- in_here(opt("out", if (quick) "quick_results" else "results"))
if (anyNA(ns) || !all(ns %in% N_GRID) || anyDuplicated(ns) || is.unsorted(ns)) stop("--n must list increasing values of the grid 1000, 1500, ..., 20000", call. = FALSE)
if (is.na(burn) || burn < 0L || is.na(nmc) || nmc < 1L || nmc %% NBATCH != 0L) stop(sprintf("--nmc must be a positive multiple of %d", NBATCH), call. = FALSE)

s <- (task - 1L) %/% 4L + 1L
cell <- CELLS[(task - 1L) %% 4L + 1L, , drop = FALSE]
dir.create(out_dir, showWarnings = FALSE, recursive = TRUE)
f_out <- file.path(out_dir, sprintf("task_%03d.csv", task))
if (file.exists(f_out)) stop("output exists, refusing to overwrite: ", f_out, call. = FALSE)
cat(sprintf("task %d: data set %d, %s; n = %s; burn %d, nmc %d; data seed %d, MCMC seed %d\n", task, s, cell$id,
            if (length(ns) == length(N_GRID)) "all 39 values" else paste(ns, collapse = ","), burn, nmc, s, 1000L + s))

# ---- fits, in increasing n
t_start <- proc.time()[["elapsed"]]
rows <- vector("list", length(ns))
for (i in seq_along(ns)) {
  n <- ns[i]; J <- J_of_n(n)
  set.seed(s); z <- rnorm(n)
  b <- build_cell(cell, n, J, z)
  r <- fit_horseshoe(cell, n, J, b, mcmc_seed = 1000L + s, burn = burn, nmc = nmc)
  rows[[i]] <- data.frame(cell = cell$id, seed = s, n = n, J = J,
    rmse_design = r$rmse_design, rmse_design_median = r$rmse_design_median, rmse_grid = r$rmse_grid,
    qhat = r$qhat, qhat_rob = r$qhat_rob, qhat_ci = r$qhat_ci, tau_hat = r$tau_hat,
    mcse_rel = r$mcse_rel, ess_logtau = r$ess_logtau, ess_f_min = min(r$ess_fpts), rhat1_f_max = max(r$rhat1_f), rhat1_logtau = r$rhat1_logtau,
    hs_fast_wall_s = r$hs_fast_wall, structure = r$structure, stringsAsFactors = FALSE)
  cat(sprintf("  n=%5d J=%4d RMSE=%.5f q=%d q_rob=%d q_CI=%d MCSE/RMSE=%.4f fit %.2f s\n", n, J, r$rmse_design,
              r$qhat, r$qhat_rob, r$qhat_ci, r$mcse_rel, r$hs_fast_wall))
  rm(b, r); invisible(gc())
}

# ---- write atomically, never replacing an existing file
tmp <- tempfile(sprintf(".task_%03d_", task), tmpdir = out_dir, fileext = ".csv")
write.csv(do.call(rbind, rows), tmp, row.names = FALSE)
if (file.exists(f_out) || !file.rename(tmp, f_out)) { unlink(tmp); stop("could not write ", f_out, " (does it exist already?)", call. = FALSE) }
cat(sprintf("task %d done: %d fits in %.1f s -> %s\n", task, length(ns), proc.time()[["elapsed"]] - t_start, f_out))
