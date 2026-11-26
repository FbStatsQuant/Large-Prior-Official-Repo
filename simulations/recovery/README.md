# Coefficient recovery

*Section 3.1 · Figure 1*

This folder runs the first numerical illustration of the paper: a regression function in the span of a large Chebyshev dictionary whose coefficient vector is only approximately sparse. There are twenty large coefficients and 980 tiny ones, each equal to 0.001, and the noise in a least-squares coefficient is about five times larger than a tiny one. One simulated data set is fitted with the Horseshoe and with ordinary least squares (OLS). The script writes every coefficient estimate with its 95% interval, and every number quoted in Section 3.1 of the paper (the errors, the interval coverage, the effective sample sizes) to a text summary.

## Running it

From this folder:

```sh
Rscript recovery.R                              # the paper's run: results/coefficients.csv, results/summary.txt
Rscript make_figure.R                           # Figure 1 from results/: figures/coef_recovery.{pdf,png}
Rscript make_figure.R --from=reference_outputs  # the same figure from the shipped reference run, no fitting
Rscript recovery.R --quick                      # smoke test with smaller sizes, writes quick_results/
```

The paper's run takes about 10 seconds (the sampler itself about 4); the first run also compiles the C++ sampler in `../../sampler/`, which takes a few seconds more. `--quick` takes a few seconds. `--out=DIR` writes to `DIR` instead. The scripts need R with Rcpp, RcppArmadillo, digest and a C++ compiler (see [`../../sampler/`](../../sampler)), and cairo graphics for the figure.

## Settings, as in the paper

| | |
|---|---|
| Dictionary and design | Chebyshev, J = 1000 columns, on n = 2000 Gauss–Chebyshev nodes (so XᵀX = nI) |
| Truth | the twenty coefficients printed in Section 3.1 (between 0.5 and 2.5), then 0.001 for k = 21, …, 1000 |
| Data | y = Xθ₀ + σz with σ = 0.2 and `set.seed(1); z <- rnorm(n)` |
| Horseshoe | half-Cauchy global scale (start 1), σ known, 2000 burn-in sweeps, 5000 saved sweeps, exact floor, `set.seed(1001)` just before `hs_fast()`; posterior means and 95% equal-tailed intervals |
| OLS | QR; 95% t-intervals with s² = RSS/(n − J) on n − J degrees of freedom (the known-σ intervals are also written) |

`--quick` uses n = 400, J = 200, 200 burn-in and 500 saved sweeps, with the same structure of truth. Its numbers are not those of the paper.

## Files

```
recovery/
├── recovery.R           the fit, the OLS fit, coefficients.csv and summary.txt
├── make_figure.R        Figure 1 from coefficients.csv only
└── reference_outputs/   a run at the paper's settings: coefficients.csv, summary.txt, coef_recovery.png, SHA256SUMS.txt
```

Running the scripts creates `results/` (or `quick_results/`) and `figures/` next to them. These are not tracked by git.

## Outputs

- `coefficients.csv`: one row per coefficient. `k`, the true `theta0`; the Horseshoe posterior mean `hs_mean`, median `hs_median`, standard deviation `hs_sd`, 95% interval `hs_lo95`, `hs_hi95`, batch-means effective sample size `hs_ess` and local scale estimate `lambda_hat`; OLS `ols` with standard error `ols_se_t` and 95% t-interval `ols_lo95_t`, `ols_hi95_t`, and the known-σ interval `ols_lo95_z`, `ols_hi95_z`.
- `summary.txt`: the settings and seeds, then the numbers of Section 3.1 in plain words: ℓ₂ errors on the twenty large coefficients, on the tail and on all; the design-point MSE (×10³); the largest and mean absolute estimate on the tail; how many of the twenty and of the 980 tail intervals contain the truth, and how many tail intervals contain zero; mean interval widths; the smallest effective sample size over the twenty large coefficients; the effective sample size of log τ; the estimate of τ; the Gram check max|XᵀX − nI|/n; the sampler seconds; and the R session.
- `figures/coef_recovery.pdf` and `.png`: Figure 1. Panel (a) shows all 1000 coefficients, (b) the first 60, and (c) the tail detail k = 21, …, 120; the annotation in (c) covers all 980 tail coefficients.

Because XᵀX = nI, the squared ℓ₂ coefficient error equals the design-point MSE; the script checks this.

## Reference outputs

`reference_outputs/` holds the outputs of `Rscript recovery.R` at the paper's settings: `coefficients.csv`, `summary.txt` and the figure as `coef_recovery.png`. They agree with the run reported in the paper to rounding error (relative differences below 2e-11, on a different machine and R version), and every number quoted in Section 3.1 matches at the printed precision. `SHA256SUMS.txt` lists their hashes (`sha256sum -c SHA256SUMS.txt` inside that folder). A rerun gives the same coefficients to rounding error; the sampler seconds and the R session lines in `summary.txt` differ. To redraw Figure 1 without fitting anything, run `Rscript make_figure.R --from=reference_outputs`. It writes to `figures/`, so the reference folder is never overwritten.
