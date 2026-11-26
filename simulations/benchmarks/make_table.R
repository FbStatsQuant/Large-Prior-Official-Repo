# make_table.R: Table 1 of the paper (Section 3.2) in paper format, from mse_long.csv only. No fitting.
#   Rscript make_table.R                           reads results/ (your own run of benchmarks.R)
#   Rscript make_table.R --from=reference_outputs  reads the shipped reference run
# Prints the table (design-point MSE multiplied by 1000, three decimals; * marks the lowest value in each column of each
# target) and writes the LaTeX rows to tables/table1_rows.tex next to this script, so the reference folder is never overwritten.
# benchmarks.R writes the same rows as table_rows.tex; this script only reformats saved numbers.
options(warn = 1)
here <- local({ a <- grep("^--file=", commandArgs(trailingOnly = FALSE), value = TRUE)
                if (length(a)) dirname(normalizePath(sub("^--file=", "", a[1L]))) else getwd() })
args <- commandArgs(trailingOnly = TRUE)
unknown <- args[!grepl("^--from=", args)]
if (length(unknown)) stop("unknown argument: ", paste(unknown, collapse = " "), " (the only option is --from=DIR)")
from <- sub("^--from=", "", grep("^--from=", args, value = TRUE))
if (length(from) > 1L) stop("give --from= once")
from <- if (length(from) == 1L) from else "results"
in_dir <- if (grepl("^(/|[A-Za-z]:)", from)) from else file.path(here, from)
f <- file.path(in_dir, "mse_long.csv")
if (!file.exists(f)) stop("missing ", f, ": run benchmarks.R first, or use --from=reference_outputs")
mse <- read.csv(f, stringsAsFactors = FALSE)

targets <- unique(mse$target); methods <- unique(mse$method); J_grid <- sort(unique(mse$J))
value <- function(tg, m, J) { v <- mse$mse_x1000[mse$target == tg & mse$method == m & mse$J == J]; stopifnot(length(v) == 1L); v }
tex <- character(0)
cat(sprintf("Design-point MSE x 1000 at n = 1000 (Table 1); * = lowest in its column for that target\n\n%-4s %-10s %s\n", "f", "Method",
            paste(sprintf("%8d", J_grid), collapse = "")))
for (tg in targets) {
  tab  <- sapply(J_grid, function(J) sapply(methods, function(m) value(tg, m, J)))      # methods x J
  best <- apply(tab, 2, which.min)
  tex  <- c(tex, sprintf("\\multirow{3}{*}{$%s_%s$}", substr(tg, 1, 1), substr(tg, 2, 2)))
  for (r in seq_along(methods)) {
    s <- sprintf("%.3f", tab[r, ])
    cat(sprintf("%-4s %-10s %s\n", tg, methods[r], paste(sprintf("%8s", ifelse(best == r, paste0(s, "*"), s)), collapse = "")))
    tex <- c(tex, sprintf("& %s", methods[r]), sprintf("& %s \\\\", paste(ifelse(best == r, sprintf("\\textbf{%s}", s), s), collapse = " & ")))
  }
  if (tg != targets[length(targets)]) tex <- c(tex, "\\midrule")
}
out_dir <- file.path(here, "tables"); dir.create(out_dir, showWarnings = FALSE)
writeLines(tex, file.path(out_dir, "table1_rows.tex"))
cat(sprintf("\nread %s\nwrote tables/table1_rows.tex (the body of Table 1)\n", file.path(from, "mse_long.csv")))
