# dictionaries.R: the design points and the three dictionaries of the paper's simulations (base R + splines).
#   source("sampler/dictionaries.R")     # stand-alone; it does not need hsfast.R
#
# design_points(design, n)       "equispaced": x_i = (i - 1) / (n - 1);  "chebyshev_nodes": x_i = (1 + cos(pi (i - 1/2) / n)) / 2
# fourier_dictionary(x, J)       1, cos(2 pi x), sin(2 pi x), cos(4 pi x), sin(4 pi x), ...  (cosine before sine; J columns)
# chebyshev_dictionary(x, J)     1, sqrt(2) T_k(2x - 1), k = 1, ..., J - 1
# bspline_dictionary(x, J)       J cubic B-splines with equally spaced knots on [0, 1]
# dictionary_matrix(basis, x, J) basis = "fourier", "chebyshev" or "bspline": the n x J design matrix (checked finite)
#
# Gram matrix G = X'X on each design (paper, Appendix "Exact Gibbs sampling for fixed dictionaries", "Exploiting the fixed design");
# this is the form hs_fast() detects and uses for the O(J) draw of theta:
#   Fourier on the equispaced design             diagonal + rank one (row n repeats row 1 of the periodic grid)
#   Chebyshev at the Gauss-Chebyshev nodes        diagonal (discrete orthogonality of T_k at the nodes)
#   Chebyshev on the equispaced design            dense (and numerically collinear for large J)
#   cubic B-splines on either design              banded, bandwidth 3

# Design points in [0, 1].
design_points <- function(design, n) {
  i <- seq_len(n)
  switch(design, equispaced = (i - 1) / (n - 1), chebyshev_nodes = 0.5 * (1 + cos(pi * (i - 0.5) / n)),
         stop("design must be \"equispaced\" or \"chebyshev_nodes\""))
}

# Real Fourier dictionary of period 1: J columns, cosine before sine in each frequency; a last cosine if J - 1 is odd.
fourier_dictionary <- function(x, J) {
  stopifnot(J >= 1)
  n <- length(x)
  B <- matrix(1, n, J); col <- 2L; k <- 1L
  while (col <= J) { B[, col] <- cos(2 * pi * k * x); col <- col + 1L
                     if (col <= J) { B[, col] <- sin(2 * pi * k * x); col <- col + 1L }; k <- k + 1L }
  B
}

# Chebyshev dictionary: column 1 = 1, column k + 1 = sqrt(2) T_k(2x - 1), k = 1..J-1, by the three-term recurrence
# T_{k+1}(t) = 2 t T_k(t) - T_{k-1}(t). Column j corresponds to coefficient index k = j - 1.
chebyshev_dictionary <- function(x, J) {
  stopifnot(J >= 2, all(x >= 0 & x <= 1))
  n <- length(x)
  t <- 2 * x - 1
  X <- matrix(0, n, J)
  Tkm1 <- rep(1, n)            # T_0
  Tk   <- t                    # T_1
  X[, 1] <- 1
  X[, 2] <- sqrt(2) * Tk
  if (J >= 3) {
    for (k in 2:(J - 1)) {
      Tkp1 <- 2 * t * Tk - Tkm1   # T_k from T_{k-1}, T_{k-2}
      X[, k + 1] <- sqrt(2) * Tkp1
      Tkm1 <- Tk
      Tk   <- Tkp1
    }
  }
  X
}

# Cubic B-splines (order 4): J functions, J - 2 equally spaced knots on [0, 1] with triple boundary knots.
bspline_dictionary <- function(x, J) {
  stopifnot(J >= 4)
  splines::splineDesign(knots = c(0, 0, 0, seq(0, 1, length.out = J - 2), 1, 1, 1), x = x, ord = 4)
}

# The n x J design matrix of one dictionary at the points x (also used for the dictionary on an evaluation grid).
dictionary_matrix <- function(basis, x, J) {
  stopifnot(J >= 5, all(x >= 0 & x <= 1))
  n <- length(x)
  X <- switch(basis,
    fourier = fourier_dictionary(x, J),
    chebyshev = chebyshev_dictionary(x, J),
    bspline = bspline_dictionary(x, J),
    stop("unknown basis ", basis))
  X <- matrix(as.numeric(X), n, J)
  if (!all(is.finite(X))) stop("dictionary_matrix: non-finite entries (", basis, ", n=", n, ", J=", J, ")", call. = FALSE)
  X
}
