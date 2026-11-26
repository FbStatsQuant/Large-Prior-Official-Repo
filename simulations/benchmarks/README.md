# Benchmarks: least squares, ridge and the Horseshoe

*Section 3.2 · Table 1 · Figure 2*

This folder compares three estimators on the same dictionary and the same data: ordinary least squares (OLS), ridge regression with the penalty chosen by cross-validation, and the Horseshoe posterior mean. Every estimator sees the same design matrix, so any difference comes from the prior alone. The script reproduces Table 1 (design-point MSE for J = 140, 160, …, 300) and the two fits of Figure 2 (J = ⌊n^0.7⌋ = 125).

| | Target | Dictionary | Design | Noise sd |
|---|---|---|---|---|
| f1 | ½ \|sin(π(x − 0.5))\| | real Fourier, period 1 | equally spaced, xᵢ = (i − 1)/(n − 1) | 0.15 |
| f2 | \|sin(1.3π(x − 0.35))\|³ | Chebyshev | Gauss–Chebyshev nodes | 0.20 |

The estimators:

- **OLS**: QR least squares on the J columns (full column rank is asserted).
- **Ridge**: minimizes ‖y − Xθ‖² + λ‖θ‖² with the constant coefficient penalized too. λ is chosen by 20-fold cross-validation over 160 values.
- **Horseshoe**: half-Cauchy global scale, noise variance known, posterior mean, computed with the exact sampler `hs_fast()` of [`../../sampler/`](../../sampler).

## Running it

From this folder:

```sh
Rscript benchmarks.R                            # the paper's run: results/
Rscript make_figure.R                           # Figure 2 from results/: figures/hs_fits.{pdf,png}
Rscript make_figure.R --from=reference_outputs  # the same figure from the shipped reference run, no fitting
Rscript make_table.R --from=reference_outputs   # Table 1 from the shipped reference run, no fitting: tables/table1_rows.tex
Rscript make_table.R                            # Table 1 from results/
Rscript benchmarks.R --quick                    # smoke test, writes quick_results/
```

The paper's run takes about 30 seconds (18 Horseshoe fits and two display fits); the first run also compiles the C++ sampler, which takes a few seconds more. `--quick` takes a few seconds. `--out=DIR` writes to `DIR` instead. The scripts need R with Rcpp, RcppArmadillo, digest and a C++ compiler (see [`../../sampler/`](../../sampler)), and cairo graphics for the figure.

## Settings, as in the paper

- n = 1000; J = 140, 160, …, 300 for Table 1; J = 125 for Figure 2.
- One simulated response per target, `set.seed(1); z <- rnorm(n)`, and y = f(x) + σz. The same z serves both targets, every J and every method.
- Horseshoe: 2000 burn-in sweeps, 5000 saved sweeps, exact floor, `set.seed(1001)` just before every `hs_fast()` call.
- Ridge folds: `make_cv_folds(n, 20, 2001)`, shared by both targets and every J.
- Error: the design-point MSE, (1/n) Σᵢ (f̂(xᵢ) − f(xᵢ))². The tables show MSE × 1000.

`--quick` uses only J = 140 and 160, 200 burn-in and 500 saved sweeps. Its numbers are not those of the paper.

## Files

```
benchmarks/
├── benchmarks.R         the three fits for both targets, Table 1, and the display fits
├── ridge.R              the cross-validated ridge (make_cv_folds(), fit_ridge_fourier())
├── make_figure.R        Figure 2 from display_points.csv and display_metrics.csv only
├── make_table.R         Table 1 in the paper's format from mse_long.csv only
└── reference_outputs/   a run at the paper's settings (see below)
```

Running the scripts creates `results/` (or `quick_results/`), `figures/` and `tables/` next to them. These are not tracked by git.

## Outputs

- `mse_long.csv`: one row per target, dictionary, J and method (OLS, Ridge, Horseshoe): `mse` and `mse_x1000`. 54 rows.
- `mse_table.csv`: the layout of Table 1. One row per target and method, one column per J, in MSE × 1000.
- `table_rows.tex`: the rows of Table 1 as LaTeX, with three decimals and the lowest value in each column of each target in bold.
- `display_points.csv`: the 1000 design points of each panel of Figure 2: `panel` (`a` is f1 with the Fourier dictionary, `b` is f2 with the Chebyshev dictionary), `x`, `truth` and `fitted`, the Horseshoe posterior mean.
- `display_metrics.csv`: the MSE of the two display fits (`mse` and `mse_x1000`), the numbers printed inside Figure 2.
- `summary.txt`: the settings and seeds, the rows of Table 1, the ridge penalty chosen in each fit, the Horseshoe diagnostics of each fit (the Gram form found by `hs_fast()`, effective sample sizes, split R-hat, Monte Carlo error) and the R session.
- `figures/hs_fits.pdf` and `.png`: Figure 2.

## Reference outputs

`reference_outputs/` holds the outputs of `Rscript benchmarks.R` at the paper's settings: the five CSV and LaTeX files and `summary.txt` above, and the figure as `hs_fits.png`. They agree with the run reported in the paper to rounding error (relative differences below 1e-13, on a different machine and R version); all 54 entries of Table 1 and the two values in Figure 2 match as printed. `SHA256SUMS.txt` lists their hashes (`sha256sum -c SHA256SUMS.txt` inside that folder). A rerun gives the same MSE values to rounding error; the timings and the R session lines in `summary.txt` differ. To redraw Figure 2 without fitting anything, run `Rscript make_figure.R --from=reference_outputs`. It writes to `figures/`, so the reference folder is never overwritten.
