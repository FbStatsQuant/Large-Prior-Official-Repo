# process.R: check the 400 task files of worker.R and bind them into one table (paper Section 3.3).
#
#   Rscript process.R                  reads results/task_*.csv, writes processed/fits_long.csv
#   Rscript process.R --partial        bind the good task files even if some are missing or bad
#   Rscript process.R --results=DIR --out=DIR --n=1000,1500
#                                      other folders; --n = the sample sizes the tasks were run with (default: all 39)
#                                      (relative folders are taken relative to this script's folder)
#
# A task file is good if it reads, has the expected columns, one row per expected n (in increasing order) with the task's
# pair, data set, n and J = floor(n^0.7), finite values, counts between 0 and J, and the Gram form the sampler must find for
# that pair. Missing and bad tasks are listed in processed/missing_tasks.txt (in sbatch --array syntax, e.g. 5,17-19) with
# the reason printed for each; without --partial the script then stops with exit status 2 and writes no table.

options(warn = 1)
here <- local({
  a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
  if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd()
})
in_here <- function(p) if (grepl("^(/|~|[A-Za-z]:)", p)) p else file.path(here, p)   # relative folders: next to this script
source(file.path(here, "..", "common.R"))        # CELLS, N_GRID, J_of_n() (also loads the compiled sampler)

args <- commandArgs(trailingOnly = TRUE)
opt <- function(name, default) {
  h <- grep(paste0("^--", name, "="), args, value = TRUE)
  if (length(h)) sub(paste0("^--", name, "="), "", h[length(h)]) else default
}
if (any(!grepl("^--(results|out|n)=|^--partial$", args)))
  stop("usage: Rscript process.R [--partial] [--results=DIR] [--out=DIR] [--n=1000,1500]", call. = FALSE)
partial <- "--partial" %in% args
results_dir <- in_here(opt("results", "results"))
out_dir <- in_here(opt("out", "processed"))
ns <- as.integer(strsplit(opt("n", paste(N_GRID, collapse = ",")), ",", fixed = TRUE)[[1]])
if (anyNA(ns) || !all(ns %in% N_GRID) || anyDuplicated(ns) || is.unsorted(ns)) stop("--n must list increasing values of the grid", call. = FALSE)
ntask <- 400L
dir.create(out_dir, showWarnings = FALSE, recursive = TRUE)
unlink(file.path(out_dir, c("missing_tasks.txt", "fits_long.csv")))

cols <- c("cell", "seed", "n", "J", "rmse_design", "rmse_design_median", "rmse_grid", "qhat", "qhat_rob", "qhat_ci", "tau_hat",
          "mcse_rel", "ess_logtau", "ess_f_min", "rhat1_f_max", "rhat1_logtau", "hs_fast_wall_s", "structure")
num_cols <- setdiff(cols, c("cell", "structure"))
Js <- vapply(ns, J_of_n, integer(1))

# The reason a task file is not usable, or "" if it is good.
check_task <- function(t, d) {
  s <- (t - 1L) %/% 4L + 1L; cl <- CELLS[(t - 1L) %% 4L + 1L, ]
  if (!identical(names(d), cols)) return("wrong columns")
  if (nrow(d) != length(ns)) return(sprintf("%d rows, expected %d", nrow(d), length(ns)))
  if (!all(d$cell == cl$id)) return(paste("pair is not", cl$id))
  if (!all(d$seed == s)) return(paste("data set is not", s))
  if (!isTRUE(all(d$n == ns))) return("sample sizes differ from the expected grid")
  if (!isTRUE(all(d$J == Js))) return("J differs from floor(n^0.7)")
  if (!all(vapply(d[num_cols], function(v) is.numeric(v) && all(is.finite(v)), NA))) return("missing or non-finite values")
  for (q in c("qhat", "qhat_rob", "qhat_ci")) if (any(d[[q]] != round(d[[q]]) | d[[q]] < 0 | d[[q]] > d$J)) return(paste(q, "is not a count in 0..J"))
  if (any(d$rmse_design <= 0 | d$rmse_design_median <= 0 | d$rmse_grid <= 0 | d$tau_hat <= 0 | d$mcse_rel < 0)) return("a value is out of range")
  if (!all(d$structure == cl$expect)) return(paste("Gram form is not", cl$expect))
  ""
}

files <- if (dir.exists(results_dir)) list.files(results_dir, pattern = "^task_[0-9]+\\.csv$") else character(0)
extra <- files[!files %in% sprintf("task_%03d.csv", seq_len(ntask))]
if (length(extra)) cat("ignoring files that are not task files of this run:", extra, "\n")
cat(sprintf("%d task files in %s\n", length(files) - length(extra), results_dir))

status <- character(ntask); rows <- list()
for (t in seq_len(ntask)) {
  f <- file.path(results_dir, sprintf("task_%03d.csv", t))
  if (!file.exists(f)) { status[t] <- "missing"; next }
  d <- tryCatch(read.csv(f, stringsAsFactors = FALSE), error = function(e) NULL)
  why <- if (is.null(d)) "unreadable" else tryCatch(check_task(t, d), error = function(e) paste("check error:", conditionMessage(e)))
  if (nzchar(why)) { status[t] <- paste("bad:", why); next }
  rows[[length(rows) + 1L]] <- d
}

compress_ids <- function(v) {                     # 1,2,3,7,9,10 -> "1-3,7,9-10"
  v <- sort(unique(as.integer(v))); if (!length(v)) return("")
  br <- c(0L, which(diff(v) != 1L), length(v))
  paste(vapply(seq_len(length(br) - 1L), function(i) { a <- v[br[i] + 1L]; b <- v[br[i + 1L]]; if (a == b) as.character(a) else paste0(a, "-", b) }, ""), collapse = ",")
}
todo <- which(nzchar(status))
cat(sprintf("tasks: %d expected, %d good, %d missing, %d bad\n", ntask, ntask - length(todo),
            sum(status == "missing"), sum(startsWith(status, "bad"))))
if (length(todo)) {
  writeLines(compress_ids(todo), file.path(out_dir, "missing_tasks.txt"))
  bad <- todo[startsWith(status[todo], "bad")]
  for (t in bad) cat(sprintf("  task %d: %s\n", t, status[t]))
  if (length(todo) > length(bad)) cat(sprintf("  missing tasks: %s\n", compress_ids(setdiff(todo, bad))))
  cat(sprintf("rerun them with: sbatch --array=%s array.slurm%s\n", compress_ids(todo), if (length(bad)) "   (delete the bad files first)" else ""))
  if (!partial) { cat("not complete: no table written (use --partial to bind the good tasks anyway)\n"); quit(save = "no", status = 2L) }
}
if (!length(rows)) stop("no good task files", call. = FALSE)

long <- do.call(rbind, rows)
long <- long[order(long$cell, long$seed, long$n), ]
write.csv(long, file.path(out_dir, "fits_long.csv"), row.names = FALSE)
cat(sprintf("%s: %d rows from %d tasks -> %s\n", if (length(todo)) "PARTIAL" else "complete", nrow(long), length(rows),
            file.path(out_dir, "fits_long.csv")))
