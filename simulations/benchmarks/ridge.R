# ridge.R: the cross-validated ridge regression of the paper (Section 3.2): 20 folds, 160 penalties, the constant column penalized too.

make_cv_folds <- function(n, nfolds, seed) {
  if (nfolds > n) {
    stop("The number of CV folds cannot exceed n.", call. = FALSE)
  }

  set.seed(seed)
  sample(rep(seq_len(nfolds), length.out = n))
}

fit_ridge_fourier <- function(y, design, foldid, nfolds) {
  # Cross-validate the exact objective printed in the paper:
  #   ||y - X beta||^2 + lambda * ||beta||^2.
  # A direct eigendecomposition is used because glmnet treats a constant
  # dictionary column as a zero-variance predictor and drops it when
  # intercept=FALSE. The direct solution penalizes every Fourier coefficient,
  # including the constant, exactly as the displayed objective states.
  design_scale <- max(diag(crossprod(design)))
  lambda_rss_grid <- design_scale * 10^seq(4, -8, length.out = 160L)
  cv_sse <- numeric(length(lambda_rss_grid))

  for (fold in seq_len(nfolds)) {
    test_index <- foldid == fold
    train_design <- design[!test_index, , drop = FALSE]
    test_design <- design[test_index, , drop = FALSE]
    train_y <- y[!test_index]
    test_y <- y[test_index]

    decomposition <- eigen(
      crossprod(train_design),
      symmetric = TRUE
    )
    rotated_score <- drop(
      crossprod(
        decomposition$vectors,
        crossprod(train_design, train_y)
      )
    )
    denominator <- outer(
      decomposition$values,
      lambda_rss_grid,
      "+"
    )
    rotated_path <- matrix(
      rotated_score,
      nrow = length(rotated_score),
      ncol = length(lambda_rss_grid)
    ) / denominator
    coefficient_path <- decomposition$vectors %*% rotated_path
    prediction_path <- test_design %*% coefficient_path
    residual_path <- sweep(prediction_path, 1L, test_y, FUN = "-")
    cv_sse <- cv_sse + colSums(residual_path^2)
  }

  selected_index <- which.min(cv_sse)
  lambda_rss <- lambda_rss_grid[selected_index]

  full_decomposition <- eigen(crossprod(design), symmetric = TRUE)
  full_rotated_score <- drop(
    crossprod(
      full_decomposition$vectors,
      crossprod(design, y)
    )
  )
  coefficients <- drop(
    full_decomposition$vectors %*%
      (full_rotated_score / (full_decomposition$values + lambda_rss))
  )

  list(
    fitted = drop(design %*% coefficients),
    coefficients = coefficients,
    lambda_rss = lambda_rss,
    # Equivalent coefficient for MSE + lambda*||beta||^2.
    lambda_per_observation = lambda_rss / nrow(design),
    cv_mse = cv_sse[selected_index] / length(y)
  )
}
