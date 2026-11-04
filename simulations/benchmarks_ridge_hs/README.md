# Ridge versus Horseshoe for the revised benchmark functions

This folder regenerates the Fourier Ridge-versus-Horseshoe comparison for the
three functions currently defined in `Overleaf Project/main.tex`.

The three entry-point scripts are:

- `function_1.R`
- `function_2.R`
- `function_3.R`

`run_all.R` runs all three in sequence. `_ridge_hs_common.R` contains the shared
fitting, plotting, and export code so the three experiments cannot drift apart.
After the full fits exist, `trend_plots.R` creates the point-estimate comparison
figures styled like the original three-panel paper figure without rerunning MCMC.

## Settings matched to the paper

- `n = 1000`
- displayed fit: `J = floor(n^0.7) = 125`
- MSE grid: `J = 140, 160, ..., 300`
- `J` is the actual number of columns in the real periodic Fourier dictionary
- known per-function noise SDs retained from the earlier simulation scripts:
  `0.15`, `0.07`, and `0.10`
- hierarchical Horseshoe with a shared half-Cauchy global scale
- coefficientwise Horseshoe posterior mean as the displayed point estimate
- ridge penalty selected with 20-fold cross-validation
- ridge is solved directly for the paper's
  `RSS + lambda * ||beta||^2` objective; every Fourier coefficient, including
  the constant, is penalized
- one fixed simulated response and one fixed set of CV folds are reused across
  all `J` values within a function

The default MCMC settings are `burn = 1000`, `nmc = 5000`, and `thin = 1`.

## Run

From this folder:

```powershell
Rscript run_all.R
```

Run one function:

```powershell
Rscript function_2.R
```

Fast validation mode:

```powershell
Rscript run_all.R --quick
```

Create the individual and combined trend-comparison plots from the saved full
results:

```powershell
Rscript trend_plots.R
```

Useful overrides include:

```text
--nmc=2000
--burn=500
--fit-J=125
--J-grid=140,160,180
--skip-grid
--output-root=/path/to/results
```

`--quick` uses a deliberately small MCMC and smaller dictionaries. Its files go
to `quick_results/`, so they do not overwrite the paper-setting outputs.

## Outputs

Each function gets its own output folder. A full run writes:

- the paper-ready fit as JPG and PDF (`f1.jpg`, `f2.jpg`, or `f3.jpg`)
- prediction-level CSV data
- displayed-fit metrics
- long and wide MSE tables
- an MSE-versus-`J` plot as JPG and PDF
- LaTeX table rows ready to paste into the paper
- a run summary with exact settings and R session details
- a manifest listing every generated artifact

The scripts do not overwrite the existing files in `Overleaf Project`; the new
assets remain in `Ridge_Hs/results/` until they have been reviewed.

The reference-style plots are written to `Ridge_Hs/trend_plots/`. The individual
files are named `f1.jpg`, `f2.jpg`, and `f3.jpg` so they can replace the current
Overleaf assets directly after review. Combined standalone and title-free
paper-ready JPG/PDF versions are also included.
