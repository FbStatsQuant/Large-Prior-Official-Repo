# hs_fast(): exact Horseshoe Gibbs sampling for fixed dictionaries

*Section 3.5 · Appendix "Exact Gibbs sampling for fixed dictionaries" · Table 3*

> **Scope.** `hs_fast()` is a function you `source()`, not an R package. It is validated for the settings of the paper's
> appendix: the designs listed there (Fourier, Chebyshev and cubic B-spline dictionaries on the equispaced design and at the
> Gauss–Chebyshev nodes, and cosine dictionaries on the equispaced design), a half-Cauchy or fixed global scale, a fixed or Jeffreys
> noise variance, and `floor = "exact"` or `floor = "package"`. The truncated half-Cauchy option of the package is not supported.
> For other designs, in particular numerically collinear or badly scaled ones, the setup checks and the dense accuracy check are
> safeguards, not a certificate of correctness.

## What it is

`hs_fast()` runs the Gibbs sampler of the R package `horseshoe`, version 0.2.0 (van der Pas, Scott, Chakraborty and Bhattacharya,
2019): the same four updates in the same order, with the same random draws. It differs in two ways.

- **Linear algebra.** Under a large series prior the dictionary and the design are fixed, so G = X'X is computed once. For the
  dictionaries of the paper G is diagonal, diagonal plus low rank, or banded, and the coefficient draw then costs O(J) per sweep
  instead of O(J³).
- **Exact posterior.** By default (`floor = "exact"`) the package's three numerical floors (on the local-scale slice, the
  global-scale slice and the noise-variance rate) are removed and the truncated draws are evaluated in a numerically stable form,
  so the chain targets the posterior itself.

With `floor = "package"` the floors are restored, and `hs_fast()` reproduces `horseshoe` 0.2.0 draw for draw from the same
`set.seed()`, up to floating-point round-off, for p ≤ n.

## Usage

From this folder:

```r
source("hsfast.R")          # compiles hs_fast.cpp on first use (under a minute), cached in .cache/
source("dictionaries.R")    # design_points(), dictionary_matrix()

n <- 2000; J <- floor(n^0.7)
x <- design_points("chebyshev_nodes", n)
X <- dictionary_matrix("chebyshev", x, J)
set.seed(1); y <- sin(4 * pi * x) * exp(-2 * x) + rnorm(n, 0, 0.1)

fit <- hs_fast(y, X, method.tau = "halfCauchy", tau = 1, method.sigma = "fixed", Sigma2 = 0.01,
               burn = 2000, nmc = 5000)
fhat <- drop(X %*% fit$BetaHat)                # posterior mean of f at the design points
info <- attr(fit, "hsfast")
info$structure                                 # "diag": the Gram form used
c(info$setup_seconds, info$sampler_seconds)
```

From the repository root, use `source("sampler/hsfast.R")` and `source("sampler/dictionaries.R")`.

**Arguments.** Those of `horseshoe::horseshoe()`: `y, X, method.tau, tau, method.sigma, Sigma2, burn, nmc, thin, alpha`, with
`method.tau` = `"fixed"` or `"halfCauchy"` and `method.sigma` = `"fixed"` or `"Jeffreys"`. Two more:

- `floor = "exact"` (default) or `"package"`, as above.
- `structure = "auto"` (default), `"diag"`, `"band"`, `"lowrank"`, `"dense"`, or a list giving the form of X'X
  (`list(kind = "diag", d = ...)`, `list(kind = "band", Gb = ..., bw = ...)`, `list(kind = "lowrank", d = ..., U = ...)`,
  `list(kind = "dense", G = ...)`). Whatever is chosen passes the setup checks below or is replaced by the dense Gram.

**Value.** The package's list (`BetaHat`, `LeftCI`, `RightCI`, `BetaMedian`, `Sigma2Hat`, `TauHat`, `BetaSamples`,
`TauSamples`, `Sigma2Samples`) plus `LambdaHat`, the posterior mean of each local scale λ_j over the saved sweeps. The attribute
`attr(fit, "hsfast")` records the floor mode, the Gram form used, the values of the three setup checks, cond(X'X) for a dense
Gram, the statistics of the dense accuracy check, the setup and sampler seconds, and the SHA-256 of the two source files.
Unlike the package, `hs_fast()` prints no progress counter.

**Errors.** `hs_fast()` stops for `method.tau = "truncatedCauchy"`; for non-finite or NA `y` or `X`, or mismatched lengths; for
a `tau` or `Sigma2` that is not one positive number; when `burn`, `nmc` and `thin` are not whole numbers or `burn` and `nmc` are
not multiples of `thin`; for `floor = "package"` with p > n (the package then switches to another algorithm); for an invalid
`structure` list; when X'X + diag(w) is not numerically positive definite; when the chain produces a non-finite value; and, in
exact mode with a dense Gram, when the accuracy check below fails.

## Gram forms and checks

What `structure = "auto"` finds (x_i = (i − 1)/(n − 1) on the equispaced design):

| Dictionary and design | Form of G = X'X | Coefficient draw per sweep |
|---|---|---|
| Fourier 1, cos 2πkx, sin 2πkx, … on the equispaced design | diagonal + rank one | O(J) |
| Cosine 1, cos πkx on the equispaced design | diagonal + rank two | O(J) |
| Chebyshev at the Gauss–Chebyshev nodes | diagonal | O(J) |
| Cubic B-splines, either design | banded, bandwidth 3 | O(J) |
| Chebyshev on the equispaced design; any other design | dense | O(J³) |

A structured form is used only if it passes three checks against the computed `crossprod(X)` at setup:

1. globally: max |G_struct − X'X| / max |X'X| ≤ 1e-10;
2. entrywise on the correlation scale: |G_struct − X'X|_jk ≤ 1e-10 √(G_jj G_kk);
3. relative to the precision: ‖G_struct − X'X‖_F ≤ 1e-8 λ_min(G_struct), or G_struct = X'X exactly. The prior only adds a
   nonnegative diagonal, so this bounds the perturbation of the conditional precision in every sweep.

If no structured form passes, `hs_fast()` says so in a message and uses the dense Gram. With a dense Gram it warns when
cond(X'X) > 1e10, and in exact mode it checks every coefficient draw: the backward error of the Cholesky factor on the drawn vector
(measured in the factor's own metric) and the residual of the mean solve must both be at most 1e-8, otherwise it stops.
`attr(fit, "hsfast")$guard` reports the largest and median values. This check adds O(J²) operations per sweep and changes no draw.
In package mode it is not run, as in `horseshoe` 0.2.0.

## Timing: Table 3

Seconds for 1000 sweeps at n = 20,000 and J = 1024, half-Cauchy global scale, fixed noise variance, `floor = "exact"`, on one core
of a shared machine (from [`reference_outputs/timing_paper.csv`](reference_outputs/timing_paper.csv)):

| Dictionary and design | Form of G | Setup | Sampler | Wall |
|---|---|---|---|---|
| Fourier, equally spaced grid | diagonal + rank one | 1.52 | 0.26 | 2.55 |
| Chebyshev, nodes | diagonal | 0.75 | 0.19 | 1.59 |
| Chebyshev, equally spaced grid | dense | 0.99 | 46.8 | 48.4 |
| B-spline, equally spaced grid | banded | 0.84 | 0.26 | 1.70 |
| B-spline, nodes | banded | 0.82 | 0.26 | 1.63 |

To print this table from the shipped numbers, without timing anything, and write its LaTeX rows to `output/table3_rows.tex`:

```sh
Rscript make_table.R                 # from reference_outputs/timing_paper.csv
```

To rerun the timings (about 2 minutes on one core; they depend on the machine and its load):

```sh
Rscript timing.R            # output/timing.csv and a printed table
Rscript timing.R --quick    # n = 2000, J = 204, 200 sweeps: a few seconds
Rscript make_table.R --from=output   # the table in the paper's format from your own run
```

**The dense design is reported twice.** The paper's row was timed without the per-sweep accuracy check of the dense draw; the
paper's caption gives 59.5 seconds for the whole call with the check on. `hs_fast()` always runs the check in exact mode, so
`timing.R` times both: the row with the check on is `hs_fast()` as it is, and the row with the check off runs the same sweeps by
calling the compiled kernel directly with the check switched off (setup and posterior summaries timed as in `hs_fast()`). The
script verifies that both give identical draws.

## Validation

Four scripts in [`checks/`](checks/) cover the paragraph "Validation" of the appendix. Each runs from `checks/`, prints what it
checks and a final line `PASS` or `FAIL` (exit status 1 on FAIL), writes a CSV to `checks/output/`, and takes `--quick` for a
smaller run. The results of the default runs are in [`reference_outputs/checks_summary.txt`](reference_outputs/checks_summary.txt).
The paper's checks used ten designs; the defaults below use small versions of the paper's designs, except where stated.

- **Linear algebra and the coefficient draw** (`Rscript check_linear_algebra.R`, about 1.5 minutes). On six designs with n = 1500 and
  J = 167 (the five pairs of Table 3 and a cosine dictionary on the equispaced design): the Gram form found against `crossprod(X)`,
  and, at a fixed state of the scales, the posterior mean A⁻¹X'y and the Cholesky factor of A = X'X + diag(w) from the structured
  routines against `solve()` and `chol()`; every relative error must be at most 1e-10. Then 10⁵ draws of the coefficient block at
  that state, whitened, must pass tests of mean, marginal distribution (Kolmogorov–Smirnov) and covariance. The paper reports
  relative errors of at most 1.9 × 10⁻¹³ on its ten designs, the largest at n = 30,000.
- **Agreement with the package** (`Rscript check_package_agreement.R`, about 10 seconds; needs `horseshoe` 0.2.0). On the same six
  designs, `hs_fast(floor = "package")` and `horseshoe::horseshoe()` run 100 sweeps from the same `set.seed()`; the series of θ, τ
  and σ² must agree to a relative difference of at most 1e-8 over the first 70 sweeps, and the state of the random number
  generator after 100 sweeps must be identical. The paper reports at most 9.4 × 10⁻¹⁰; the shipped default run gave at most
  2.7 × 10⁻⁹ (round-off differences of this size can vary between machines). The paper's second comparison, of the exact
  mode against a copy of the package with only the floors removed, is not shipped, since it needs that modified package.
- **Joint-distribution tests** (`Rscript check_geweke.R`, about 1.5 minutes plus about 1 minute to compile on first use). Per-block tests in the sense of Geweke (2004) of the exact
  mode on a small cosine design (diagonal plus low-rank Gram), under a half-Cauchy global scale with random or fixed noise variance,
  and two deliberately introduced errors, in the local-scale and global-scale updates, that the tests must detect. The test driver
  `geweke_driver.cpp` is compiled together with the text of `hs_fast.cpp`; the errors are made on a copy of that text. The default
  is the paper's run (10⁶ replicates per clean case): the paper reports a largest |z| of 2.56 against the Bonferroni cutoff 4.06,
  and the errors detected with |z| of 74 and more. `--quick` uses 10⁵ and 2 × 10⁴ replicates.
- **Reproduction** (`Rscript check_reproduction.R`, about 20 seconds). Data sets with n = 20,000 on a cosine dictionary with 1024
  frequencies were fitted earlier with the package; their RMSEs are in
  [`reference_outputs/package_rmse_n20000.csv`](reference_outputs/package_rmse_n20000.csv). `hs_fast(floor = "package")` refits
  them from the same seeds and must reproduce every RMSE to a relative difference of at most 1e-6. The default runs seeds 1–5;
  `--seeds=100` runs all 100 data sets, as in the paper (about 6 minutes), where the largest relative difference was 2 × 10⁻¹⁴.

These checks establish that the chain targets the posterior; they say nothing about how fast it mixes, which is that of the
package.

## Files

```
sampler/
├── README.md
├── hsfast.R                     defines hs_fast(); source() it
├── hs_fast.cpp                  the Gibbs kernel (Rcpp / RcppArmadillo), compiled on first source()
├── dictionaries.R               design points; Fourier, Chebyshev and cubic B-spline dictionaries
├── timing.R                     Table 3: the timings
├── make_table.R                 Table 3 in the paper's format, from a saved timing CSV
├── checks/
│   ├── common.R                 shared code of the four checks
│   ├── check_linear_algebra.R
│   ├── check_package_agreement.R
│   ├── check_geweke.R
│   ├── geweke_driver.cpp        test driver of check_geweke.R
│   └── check_reproduction.R
├── reference_outputs/
│   ├── timing_paper.csv         the numbers of Table 3
│   ├── package_rmse_n20000.csv  RMSEs of the earlier package fits (check_reproduction.R)
│   └── checks_summary.txt       results of the default runs of the four checks
├── SHA256SUMS.txt               hashes of hsfast.R, hs_fast.cpp and dictionaries.R
└── LICENSE                      GPL-3
```

**Requirements.** R with a C++ compiler and the packages `Rcpp`, `RcppArmadillo` and `digest` (`splines` ships with R); the
package `horseshoe` 0.2.0 only for `check_package_agreement.R`. That package is archived on CRAN; install it with
`install.packages("https://cran.r-project.org/src/contrib/Archive/horseshoe/horseshoe_0.2.0.tar.gz", repos = NULL, type = "source")`. On first `source()`, `hsfast.R` compiles `hs_fast.cpp` into
`.cache/` (keyed by the file's content); the folder is safe to delete. `check_geweke.R` keeps its own compiled versions in
`checks/output/cache/`. To verify the source files, run `sha256sum -c SHA256SUMS.txt` in this folder.

## License and credit

This folder is distributed under the GNU General Public License, version 3 ([`LICENSE`](LICENSE)), because `hsfast.R` and
`hs_fast.cpp` adapt code from the R package `horseshoe` 0.2.0 by Stéphanie van der Pas, James Scott, Antik Chakraborty and Anirban
Bhattacharya (GPL-3):

> van der Pas, S., Scott, J., Chakraborty, A. and Bhattacharya, A. (2019). *horseshoe: Implementation of the Horseshoe Prior*.
> R package version 0.2.0. https://doi.org/10.32614/CRAN.package.horseshoe

The rest of the repository is under the MIT license ([`../LICENSE`](../LICENSE)).
