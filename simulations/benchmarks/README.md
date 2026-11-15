# Benchmarks: Horseshoe vs. ridge (Section 3.1, Figure 1, Table 1)

This folder fits the same real Fourier dictionary two ways and compares them on three periodic test functions. The two fits are a Horseshoe prior and ridge regression with a cross-validated penalty. Because the dictionary is shared, the comparison isolates the regularization.

| | Target | Noise sd |
|---|---|---|
| f1 | 0.5 \|sin(π(x − 0.5))\| | 0.15 |
| f2 | \|sin(π(x − 0.3))\|³ + 0.7 \|sin(π(x − 0.7))\|³ | 0.07 |
| f3 | \|sin(π(x − 0.2))\|⁵ + \|sin(π(x − 0.5))\|⁵ + 0.6 \|sin(π(x − 0.9))\|⁵ | 0.10 |

## Files

| File | What it does |
|---|---|
| `function_1.R`, `function_2.R`, `function_3.R` | one target each: simulate, fit, write results |
| `run_all.R` | runs the three in turn |
| `trend_plots.R` | draws Figure 1 from saved results, without rerunning the MCMC |
| `_ridge_hs_common.R` | shared code: the dictionary, both fits, MSE tables, plots |
| `reference_outputs/` | outputs of the paper run (see below) |

## Running it

```sh
Rscript run_all.R          # writes results/function_{1,2,3}/   (30–60 min per function)
Rscript trend_plots.R      # writes trend_plots/                (seconds)
```

To redraw Figure 1 without the MCMC, copy `reference_outputs/` to `results/` and run `trend_plots.R`. The paper's figure is `trend_plots/ridge_hs_trend_comparison_paper.jpg`, and it comes out byte-identical to the one in the manuscript.

`Rscript run_all.R --quick` is a fast smoke test with a short chain and small dictionaries. It writes to `quick_results/` so it never overwrites the full run. A single target can be run with `Rscript function_2.R`. Other options:

```
--nmc=2000  --burn=500  --fit-J=125  --J-grid=140,160,180  --skip-grid  --output-root=/path/to/results
```

## Settings (as in the paper)

- n = 1000 equally spaced points, with one simulated response per target (seed 1991). That response is reused for every J.
- Figure 1 uses J = ⌊n^0.7⌋ = 125. Table 1 uses J = 140, 160, …, 300. J is the number of columns of the real Fourier dictionary: the constant, sine–cosine pairs, and one extra cosine when J is even.
- Horseshoe: σ known, half-Cauchy global scale, 1000 burn-in iterations and then 5000 draws. The estimate is the coefficientwise posterior mean.
- Ridge: minimizes RSS + λ‖θ‖², with the constant term also penalized. λ is chosen by 20-fold CV over 160 values.

## Outputs

Each `results/function_k/` gets the following files:

- the fitted curves: `f*_predictions.csv`, with the plots as JPG and PDF;
- the error tables: `f*_display_metrics.csv` (Figure 1's MSE values), `f*_mse_long.csv` and `f*_mse_table.csv`;
- `f*_table_rows.tex`: Table 1's rows, ready to paste into LaTeX;
- `f*_summary.txt`: the exact settings and `sessionInfo()`.

`reference_outputs/` holds these files from the paper run. All 54 entries of Table 1 and the six MSE values quoted under Figure 1 match them. `reference_outputs/paper_figure_data/` combines the three functions in one place.
