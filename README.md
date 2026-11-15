# Large series priors

Code and Lean proofs for the paper **Large series priors for adaptive and optimal Bayesian nonparametric regression** by Felipe Bedoya and Meng Li (Department of Statistics, Rice University).

[![R 4.4.1](https://img.shields.io/badge/R-4.4.1-276DC3)](https://www.r-project.org/)
[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0--rc2-0f4c81)](https://lean-lang.org/)
[![License: MIT](https://img.shields.io/badge/license-MIT-lightgrey)](LICENSE)

## The idea

Random series priors usually need a prior on the number of terms, and that means sampling across models of different dimension. We skip that step. The regression function is expanded in a **large, fixed** number of basis functions, J_n ≍ n^b (Fourier or B-splines), and a **Horseshoe prior** on the coefficients does the work of deciding which terms matter. Once the basis is fixed, the posterior is that of an ordinary Bayesian linear regression, so any Horseshoe sampler can fit it.

On the theory side, Theorem 1 gives posterior contraction for product shrinkage priors under prior-mass conditions adapted from Wei and Ghosal (2020). Corollary 1 turns this into adaptive, near-minimax rates over anisotropic Hölder-type classes, using one prior that is fixed in advance. The rate is driven mainly by how sparsely the basis represents the true function.

## What's here

| Folder | In the paper | Contents |
|---|---|---|
| [`simulations/benchmarks/`](simulations/benchmarks) | Section 3.1: Figure 1, Table 1 | Horseshoe vs. ridge on three benchmark functions, same Fourier dictionary |
| [`simulations/scaling/`](simulations/scaling) | Section 3.2: Table 2 | how the error and the active-coefficient count grow with n, cosine vs. B-spline basis (SLURM) |
| [`applications/`](applications) | Section 3.3: Figure 2 | sunspots, bike rentals, and ocean wave heights |
| [`lean/`](lean) | Theorem 1, Corollary 1, Appendix D | machine-checked proofs in Lean 4 with Mathlib |

Each folder has its own README with the settings, the commands to run, and what the outputs are.

## Reproducing the paper

| Paper item | Run | Time | Reference outputs |
|---|---|---|---|
| Figure 1, Table 1 | `simulations/benchmarks/run_all.R`, then `trend_plots.R` | 30–60 min per function | included; Figure 1 is byte-identical, and all 54 Table 1 entries match |
| Table 2 | `simulations/scaling/`: SLURM arrays, then `table2_slopes.R` | 15,500 cluster tasks | processed f1 outputs included |
| Figure 2 | `applications/code/prep_*.R`, `run_applications.R`, `make_figure.R` | about 45 min | run summaries and the buoy fit included |
| Theorem 1, Corollary 1 | `lean/`: `lake build`, then `lake env lean AxiomCheck.lean` | about 15 min with the Mathlib cache | builds with no `sorry`, standard axioms only |

Every R script runs from its own folder and writes next to itself, so no paths need editing.

**Requirements.** The paper runs used R 4.4.1 with [`horseshoe`](https://CRAN.R-project.org/package=horseshoe) 0.2.0 for every MCMC fit, `ggplot2` for figures, and `digest` for the data checksums; `splines` ships with R. The cluster runs used R 4.5.2. The Lean part needs [elan](https://github.com/leanprover/elan), which installs the pinned toolchain automatically.

## Data

The three applications use public data. NOAA's buoy files are included. The SILSO sunspot series and the UCI bike-sharing data are downloaded by the prep scripts and checked against the hashes of the paper's run. Sources and citations are in [`applications/README.md`](applications/README.md).

## Citation and license

`CITATION.cff` has the reference; GitHub shows it under "Cite this repository". The code and Lean sources are MIT-licensed (see [`LICENSE`](LICENSE)). The third-party data stay under their providers' terms.

Questions and issues are welcome through GitHub issues.
