# Empirical scaling

*Section 3.3 · Table 2 · Figure 3*

This folder runs the scaling experiment of the paper: how the error of the posterior mean and the number of active coefficients change with the sample size n. Each of the two targets is fitted with two dictionaries on the same data: its global dictionary (Fourier for f1 on equally spaced points, Chebyshev for f2 on the Gauss–Chebyshev nodes) and cubic B-splines with equally spaced knots. There are 39 sample sizes, n = 1000, 1500, …, 20000, with J_n = ⌊n^0.7⌋ columns, so J_n grows from 125 to 1024. Each n has 100 simulated data sets. That makes 4 × 39 × 100 = 15,600 Horseshoe fits.

For each fit the worker records the RMSE of the posterior mean at the design points (and on a uniform grid of 2000 points), and three counts of active coefficients:

- q̂: coefficients whose posterior mean exceeds 1/J_n in absolute value;
- q̂^rob: the same with the threshold max{1/J_n, σ√(2 log J_n / n) / ‖ξ_j‖_{2,n}}, the universal threshold on the scale of column j;
- q̂^CI: coefficients whose 95% credible interval excludes zero.

The rate in Table 2 is the least-squares slope of log(mean RMSE over the 100 data sets) on log n. The γ̂ columns are the same slopes for the mean counts.

## Running it

From this folder. **From the shipped results** (seconds, no fitting, no compiler needed):

```sh
Rscript summarize.R --from=reference_outputs     # Table 2 and every number of the text: summary/
Rscript make_figures.R --from=reference_outputs  # Figure 3: figures/scaling_f1.{pdf,png}, scaling_f2.{pdf,png}
```

**One task on a laptop** (about 1–1.5 minutes; the first run also compiles the C++ sampler in `../../sampler/`):

```sh
Rscript worker.R 1                  # data set 1, f1 with the Fourier dictionary, all 39 n: results/task_001.csv
Rscript worker.R 1 --n=1000,1500    # only these sample sizes (a few seconds)
Rscript worker.R 1 --quick          # smoke test: n = 1000, 1500 with 200 burn-in and 500 saved sweeps, written to quick_results/
```

**The full experiment on a SLURM cluster** (400 tasks of about 70 s each, about 8 core-hours in all). Edit the account, partition and module lines of the two `.slurm` files, then:

```sh
mkdir -p logs
Rscript worker.R 1 --quick          # compile the sampler once before the array starts
sbatch array.slurm                  # tasks 1-400, at most 40 at a time
sbatch --dependency=afterany:<array job id> process.slurm   # process.R, summarize.R, make_figures.R
```

`process.R` checks every task file (expected pair, data set, sample sizes, J, finite values, counts between 0 and J, the Gram form the sampler must find) and binds them into `processed/fits_long.csv`. If tasks are missing or bad, it lists them in `processed/missing_tasks.txt`, prints the `sbatch --array=…` line that reruns them, and stops; `--partial` binds the good ones anyway. Without a cluster, the same steps are `Rscript worker.R T` for T = 1, …, 400, then `Rscript process.R`, `Rscript summarize.R` and `Rscript make_figures.R`.

The scripts need R with Rcpp, RcppArmadillo, digest and a C++ compiler for the fits (see [`../../sampler/`](../../sampler)), and cairo graphics for the figures. `summarize.R` and `make_figures.R` use base R only.

## Settings, as in the paper

| | |
|---|---|
| Targets | f1(x) = 0.5 \|sin(π(x − 0.5))\|, σ = 0.15; f2(x) = \|sin(1.3π(x − 0.35))\|³, σ = 0.20 |
| Pairs | `f1_fourier`, `f1_bspline` (equally spaced x); `f2_chebyshev`, `f2_bspline` (Gauss–Chebyshev nodes) |
| Sizes | n = 1000, 1500, …, 20000 (39 values); J_n = ⌊n^0.7⌋ columns, intercept included |
| Horseshoe | half-Cauchy global scale (start 1), σ² fixed at its true value, 2000 burn-in and 5000 saved sweeps, one chain, exact floor, Gram form found by `hs_fast()` |
| Data sets | 100 per n; both dictionaries of a target are fitted to the same data |

## Tasks and seeds

Task T (1–400) is data set s = (T − 1) %/% 4 + 1 and pair (`f1_fourier`, `f1_bspline`, `f2_chebyshev`, `f2_bspline`)[(T − 1) %% 4 + 1], so tasks 1–4 are data set 1 and tasks 397–400 are data set 100. A task fits all 39 sample sizes in increasing order. For each n the noise is `set.seed(s); z <- rnorm(n)`, the same vector for both targets and both dictionaries, and `set.seed(1000 + s)` is called immediately before the sampler. The same 100 seeds are used at every n, so the results at different n are not independent; the standard errors of the slopes are descriptive only.

## Files

```
scaling/
├── worker.R           one task: 39 fits, written to results/task_TTT.csv (one row per n)
├── process.R          checks the 400 task files and binds them into processed/fits_long.csv
├── summarize.R        Table 2, the per-n summaries, the slopes, the diagnostics and summary.txt
├── make_figures.R     Figure 3 from by_n.csv and results_table.csv
├── array.slurm        SLURM array template (tasks 1-400)
├── process.slurm      SLURM template for process.R, summarize.R and make_figures.R
└── reference_outputs/ the paper run (see below)
```

The scripts share `../common.R` (targets, J rule, pairs, the Horseshoe fit and its diagnostics). Running them creates `results/`, `quick_results/`, `processed/`, `summary/`, `figures/` and `logs/` next to them. These are not tracked by git. Relative folders given to `--out`, `--from` or `--results` are taken relative to this folder.

## Outputs

- `fits_long.csv`: one row per fit. `cell` (the pair), `seed` (the data set), `n`, `J`; `rmse_design` (posterior mean at the design points), `rmse_design_median` (posterior median), `rmse_grid` (posterior mean on the grid (m − ½)/2000); the counts `qhat`, `qhat_rob`, `qhat_ci`; `tau_hat`; MCMC diagnostics: `mcse_rel` (batch-means Monte Carlo standard error of the fitted values, root mean square over the design points, divided by the RMSE), `ess_logtau`, `ess_f_min` (smallest effective sample size of the fitted value at the design points nearest x = 0.1, 0.3, 0.5, 0.7, 0.9), `rhat1_f_max` and `rhat1_logtau` (single-chain split R̂); `hs_fast_wall_s` (seconds for the whole sampler call, setup and posterior summaries included); `structure` (the Gram form used: `lowrank`, `band` or `diag`).
- `by_n.csv`: per pair and n, over the data sets: mean, sd, standard error, median and 10% / 90% quantiles of both RMSEs and of the three counts; median and largest `mcse_rel`, smallest `ess_f_min`, median `ess_logtau`.
- `results_table.csv`: per pair and quantity, the slope on log n of the log of the mean (`estimate`, `se`, `r2`, 95% interval), the slope of the log of the median, and the median and quartiles of the per-data-set slopes. Quantities: `raw` (the rate), `adjusted` (log mean RMSE − ½ log log n), `raw_grid` and `adjusted_grid` (the same on the uniform grid), `gamma_q`, `gamma_q_rob`, `gamma_q_ci`.
- `per_seed_slopes.csv`: every slope for every data set. `diagnostics.csv`: per pair, Monte Carlo error, effective sample sizes, largest R̂, total sampler seconds.
- `table2.csv` and `table_rows.tex`: the four rows of Table 2 (rate and the three γ̂, with standard errors; the adjusted rate is kept as a column).
- `wall_times.csv`: median, smallest and largest sampler wall time per pair and n (the times quoted in Section 3.5 and in the appendix on exact Gibbs sampling).
- `summary.txt`: the settings, then every number quoted in Section 3.3 and the wall times of Section 3.5 and the appendix, in plain words, each with the paper's rounding next to the full value.
- `figures/scaling_f1` and `scaling_f2` (`.pdf`, `.png`): Figure 3, panels (a) and (b). Points are means over the data sets with ±2 standard errors, bands span the 10% and 90% quantiles, lines are the least-squares fits; the legend gives the rate. `make_figures.R` recomputes each rate from `by_n.csv` and stops if it differs from `results_table.csv`.

## Reference outputs

`reference_outputs/` holds the paper run: `fits_long.csv` with all 15,600 per-fit rows, and the outputs of `Rscript summarize.R --from=reference_outputs` (`by_n.csv`, `results_table.csv`, `per_seed_slopes.csv`, `diagnostics.csv`, `table2.csv`, `table_rows.tex`, `wall_times.csv`, `summary.txt`) and of `Rscript make_figures.R --from=reference_outputs` (`scaling_f1.png`, `scaling_f2.png`). No raw fits (coefficient vectors or chains) are shipped. Every number of Table 2 and of the Section 3.3 text can be read from `summary.txt`. `SHA256SUMS.txt` lists the hashes (`sha256sum -c SHA256SUMS.txt` inside that folder).

A rerun of a task reproduces the RMSEs, counts and τ̂ of the reference rows to rounding error (relative differences of order 1e-15 for data set 1 at n = 1000 and 1500). The wall times depend on the machine: the paper's were measured on one core of a computing cluster.
