# common.R: shared code of the four validation scripts in this folder (sourced by them; not run on its own).
# Loads hs_fast() and the dictionaries, reads the command-line flags, builds the small test designs, and writes the outputs.

source(file.path(HERE, "..", "hsfast.R"))
source(file.path(HERE, "..", "dictionaries.R"))
OUT <- file.path(HERE, "output")
dir.create(OUT, showWarnings = FALSE)

ARGS <- commandArgs(TRUE)
has_flag <- function(name) any(ARGS == paste0("--", name))
flag_value <- function(name, default) {           # --name=value, or the default
  v <- sub(paste0("^--", name, "="), "", grep(paste0("^--", name, "="), ARGS, value = TRUE))
  if (length(v)) as.numeric(v[1]) else default
}
QUICK <- has_flag("quick")

# Cosine dictionary on [0, 1]: J columns 1, cos(pi k x), k = 1, ..., J - 1. Its Gram matrix on the equispaced design is
# diagonal plus rank two (the end points x = 0 and x = 1 add the rank-two term).
cosine_dictionary <- function(x, J) {
  X <- matrix(1, length(x), J)
  for (k in seq_len(J - 1)) X[, k + 1] <- cos(pi * k * x)
  X
}

# The small test designs: the five dictionary and design pairs of Table 3 of the paper, plus a cosine dictionary on the
# equispaced design; n points, J = floor(n^0.7) columns. Data as in timing.R: f0(x) = sin(4 pi x) exp(-2x), y = f0 + N(0, 0.1^2),
# set.seed(20261125). 'form' is the form of X'X that hs_fast() must find.
DESIGNS <- data.frame(
  name   = c("fourier_equispaced", "chebyshev_nodes", "chebyshev_equispaced", "bspline_equispaced", "bspline_nodes", "cosine_equispaced"),
  basis  = c("fourier", "chebyshev", "chebyshev", "bspline", "bspline", "cosine"),
  design = c("equispaced", "chebyshev_nodes", "equispaced", "equispaced", "chebyshev_nodes", "equispaced"),
  form   = c("lowrank", "diag", "dense", "band", "band", "lowrank"),
  stringsAsFactors = FALSE)
small_design <- function(i, n) {
  J <- as.integer(floor(n^0.7)); d <- DESIGNS[i, ]
  x <- design_points(d$design, n)
  X <- if (d$basis == "cosine") cosine_dictionary(x, J) else dictionary_matrix(d$basis, x, J)
  set.seed(20261125L); f0 <- sin(4 * pi * x) * exp(-2 * x); y <- f0 + rnorm(n, 0, 0.1)
  list(name = d$name, form = d$form, n = n, J = J, x = x, X = X, y = y)
}

write_out <- function(tab, file) {
  write.csv(tab, file.path(OUT, file), row.names = FALSE)
  cat("wrote", file.path("output", file), "\n")
}
finish <- function(pass) {
  cat(if (pass) "PASS\n" else "FAIL\n")
  quit(save = "no", status = if (pass) 0 else 1)
}
