# Simulations

The three simulation studies of Section 3 of the paper. All Horseshoe fits here use [`hs_fast()`](../sampler), the sampler of Section 3.5.

- [`recovery/`](recovery): how the posterior treats a coefficient vector with twenty large entries and 980 tiny ones (Section 3.1, Figure 1). One fit; runs in about 10 seconds.
- [`benchmarks/`](benchmarks): Horseshoe against least squares and cross-validated ridge on the same dictionary, as the dictionary grows (Section 3.2, Table 1, Figure 2). Runs in about 30 seconds.
- [`scaling/`](scaling): how the error and the number of active coefficients change with n, from 1,000 to 20,000, for a global dictionary and for B-splines (Section 3.3, Table 2, Figure 3). The full experiment is set up for a SLURM cluster; the shipped per-fit results reproduce the table and the figure in seconds.

[`common.R`](common.R) holds what the three share: the two target functions and their noise levels, the rule J_n = ⌊n^0.7⌋, the four pairs of target, dictionary and design, the Horseshoe fit with its summaries and diagnostics, and the figure style. The dictionaries themselves (Fourier, Chebyshev, cubic B-splines) and the two designs (equally spaced points, Gauss–Chebyshev nodes) are in [`../sampler/dictionaries.R`](../sampler/dictionaries.R).

| | Target | Regularity | Noise sd | Global dictionary | Design |
|---|---|---|---|---|---|
| f1 | 0.5 \|sin(π(x − 0.5))\| | α = 1 | 0.15 | Fourier | equally spaced |
| f2 | \|sin(1.3π(x − 0.35))\|³ | α = 3 | 0.20 | Chebyshev | Gauss–Chebyshev nodes |

Each script runs from its own folder with plain `Rscript` and writes next to itself. The scripts that fit a model (`recovery.R`, `benchmarks.R`, `scaling/worker.R`) accept `--quick` for a fast smoke test; the scripts that only summarize, tabulate or draw read saved results and take `--from=reference_outputs` instead. Each folder ships `reference_outputs/` to compare against: for `scaling/` the per-fit results of the paper's run, for the other two a rerun at the paper's settings that agrees with the paper's run to rounding error.

The scripts of the earlier version of the paper (three periodic targets with a cosine dictionary) are no longer part of the tree; they remain in the repository's history.
