# make_table.R: Table 3 of the paper (appendix on exact Gibbs sampling) in paper format, from a saved timing CSV. No timing.
#   Rscript make_table.R                 reads reference_outputs/timing_paper.csv (the paper's numbers)
#   Rscript make_table.R --from=output   reads output/timing.csv (your own run of timing.R)
# Prints the table (seconds for 1000 sweeps: setup, sampler, wall) and writes the LaTeX rows to output/table3_rows.tex.
# The dense design has two rows in the CSV: the table shows the one timed without the per-sweep accuracy check, as in the
# paper, and the wall time with the check on is printed below it (the paper gives it in the caption).
f <- sub("^--file=", "", grep("^--file=", commandArgs(FALSE), value = TRUE)[1])
HERE <- if (!is.na(f)) dirname(normalizePath(f)) else getwd()
args <- commandArgs(TRUE)
unknown <- args[!grepl("^--from=", args)]
if (length(unknown)) stop("unknown argument: ", paste(unknown, collapse = " "), " (the only option is --from=reference_outputs or --from=output)")
from <- sub("^--from=", "", grep("^--from=", args, value = TRUE))
from <- if (length(from) == 1L) from else "reference_outputs"
csv <- switch(from, reference_outputs = "timing_paper.csv", output = "timing.csv",
              stop("--from must be reference_outputs or output"))
path <- file.path(HERE, from, csv)
if (!file.exists(path)) stop("missing ", path, if (from == "output") ": run timing.R first" else "")
tab <- read.csv(path, stringsAsFactors = FALSE)

DESIGN <- c("equispaced grid" = "equally spaced grid", "Gauss-Chebyshev nodes" = "nodes")
secs <- function(v) ifelse(is.na(v), "", ifelse(v >= 10, sprintf("%.1f", v), sprintf("%.2f", v)))   # three significant digits, as printed
rows <- tab[tab$accuracy_check != "on", ]
label <- sprintf("%s, %s", rows$dictionary, DESIGN[rows$design])
cat(sprintf("Seconds for %d sweeps at n = %d, J = %d (Table 3)\n\n%-32s %-20s %7s %8s %7s\n", rows$sweeps[1], rows$n[1], rows$J[1],
            "Dictionary and design", "Form of G", "Setup", "Sampler", "Wall"))
cat(sprintf("%-32s %-20s %7s %8s %7s\n", label, rows$gram_form, secs(rows$setup_s), secs(rows$sampler_s), secs(rows$wall_s)), sep = "")
on <- tab[tab$accuracy_check == "on", ]
if (nrow(on)) cat(sprintf("\nDense design with the per-sweep accuracy check on: the whole call took %s seconds.\n", secs(on$wall_s)))
tex <- sprintf("%s & %s & %s & %s & %s \\\\", label, rows$gram_form, secs(rows$setup_s), secs(rows$sampler_s), secs(rows$wall_s))
out_dir <- file.path(HERE, "output"); dir.create(out_dir, showWarnings = FALSE)
writeLines(tex, file.path(out_dir, "table3_rows.tex"))
cat(sprintf("\nread %s/%s\nwrote output/table3_rows.tex (the body of Table 3)\n", from, csv))
