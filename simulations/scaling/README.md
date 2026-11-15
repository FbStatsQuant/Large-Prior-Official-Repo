# Scaling experiment

*Section 3.2 · Table 2*

How do the error of the posterior mean and the number of non-negligible coefficients grow with n, for a cosine basis versus a cubic B-spline basis? This folder runs that experiment. Each (n, data set) pair is a separate job, so it is set up as SLURM array jobs. We ran it on Rice's NOTS cluster.

## Files

```
scaling/
├── F1/  F2/  F3/          one folder per target function
│   ├── F*_worker.R        one (n, seed) pair: simulate, fit both bases, save the coefficients
│   ├── F*_process.R       turn all saved fits into one CSV per basis (RMSE and coefficient counts)
│   └── F*_array.slurm     the SLURM array that runs every worker task
├── process_all.slurm      runs F*_process.R for F1–F3 once every worker has finished
├── table2_slopes.R        the log–log slopes reported in Table 2
└── reference_outputs/F1/  processed CSVs for f1 from our cluster run
```

`F1/` also contains two optional scripts. `F1_array_tail.slurm` resubmits tasks 5001–5900 (the largest n) on their own, and `F1_process.slurm` processes F1 alone.

## The setup

Every task simulates a data set, fits the Horseshoe with two bases, and saves the posterior means and medians of the coefficients. The design is equally spaced on [0, 1], J_n = ⌊n^0.7⌋, and σ² is treated as known.

- **Cosine basis:** 1, cos(πx), …, cos(πJ_n x), which is J_n + 1 columns. The global scale τ is fixed. In file and variable names this basis is called `fourier`.
- **B-spline basis:** cubic, `splines::bs(x, df = J_n, intercept = TRUE)`, which is J_n columns. The global scale has a half-Cauchy prior.

| | f1 | f2 | f3 |
|---|---|---|---|
| Target | 0.5 \|cos(πx)\| | periodized Bernoulli polynomial B₄, two shifted copies | periodized B₆, three shifted copies |
| Nominal regularity m | 1 | 3 | 5 |
| Noise sd | 0.15 | 0.07 | 0.09 |
| n in the worker | 1000, 1500, …, 30000 | 1000, 1500, …, 30000 | 400, 800, …, 14800 |
| Data sets per n | 100 (seeds 1–100) | 100 | 100 |
| Cosine τ (fixed) | n^−1.2 | n^−0.9 | n^−1 |
| MCMC (burn + draws) | 2000 + 5000 | 2000 + 5000 | 2000 + 6000 cosine, 2000 + 5000 B-spline |
| Array tasks | 5,900 | 5,900 | 3,700 |

The exact formulas for the targets are at the top of each `F*_worker.R`. The same formula is repeated in `F*_process.R`, which needs it to compute the error. f1 is the same function as in Section 3.1; f2 and f3 are not the benchmark targets of Section 3.1.

From the saved coefficients, `F*_process.R` rebuilds the fitted curve at the design points and records:

- `rmse_mean`: ‖f̂ − f₀‖_{2,n} for the posterior mean. `rmse_median` is the same for the posterior median.
- `a1`, `a2`, `a3`: how many posterior-mean coefficients exceed 1/√J_n, 1/J_n and 1/(J_n√n) in absolute value. Table 2 uses `a2`, the count above 1/J_n.

`table2_slopes.R` takes the median across data sets at each n and regresses on log n over n = 1000, 1500, …, 20000. It reports the raw slope of log RMSE, the slope after subtracting ½ log log n, and γ̂_q, the slope of the log count.

## Running it

On a SLURM cluster, from this folder:

```sh
cd F1 && mkdir -p logs && sbatch F1_array.slurm && cd ..   # likewise F2, F3
mkdir -p logs && sbatch process_all.slurm                  # after all workers finish
Rscript table2_slopes.R
```

The `#SBATCH --account/--partition` lines and the `module load` lines are specific to NOTS, so change them for your cluster. A task takes from about 30 seconds at n = 1000 up to an hour at n = 30000. The memory requests in the `.slurm` files are sized for the largest n.

To try a single task on a laptop:

```sh
Rscript F1/F1_worker.R 1     # task 1 = (n = 1000, seed 1), about 2 minutes
Rscript F1/F1_process.R      # writes F1/processed/F1_{fourier,spline}.csv
```

Task `i` maps to `n = n_seq[(i - 1) %/% 100 + 1]` and `seed = (i - 1) %% 100 + 1`. Set `LP_RESULTS_DIR` and `LP_PROCESSED_DIR` to write somewhere other than `results/` and `processed/` next to the scripts.

## Reference outputs

The raw `.rds` fits (thousands of files) are not included. `reference_outputs/F1/` holds the processed f1 CSVs from our cluster run, with 100 data sets at each n = 1000, 1500, …, 23500; rerunning task 1 locally reproduces its row to machine precision. To compute the slopes from these files:

```sh
Rscript table2_slopes.R --processed=reference_outputs/F1 --functions=F1
```

**Reproducibility note.** The script that computed the published slopes was not kept, so `table2_slopes.R` recomputes them from the rules stated in Section 3.2. On the f1 files above it gives raw and adjusted slopes of −0.153 and −0.211 (B-spline) and −0.331 and −0.389 (cosine), within 0.002 of Table 2. The count slopes γ̂_q are 0.705 and 0.206, against 0.707 and 0.241 in Table 2. The grid in `F3_worker.R` (n = 400, 800, …, 14800) differs from the grid of Table 2 (n = 1000, 1500, …, 20000).
