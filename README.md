# Large series priors

[![R 4.4.1](https://img.shields.io/badge/R-4.4.1-276DC3)](https://www.r-project.org/)
[![Lean 4](https://img.shields.io/badge/Lean-v4.35.0--rc2-0f4c81)](https://lean-lang.org/)
[![License: MIT](https://img.shields.io/badge/license-MIT-lightgrey)](LICENSE)

This repository has the code and Lean proofs for **Large series priors for adaptive and optimal Bayesian nonparametric regression**, by Felipe Bedoya and Meng Li (Department of Statistics, Rice University).

## The idea

A random series prior usually needs a prior on the number of terms, and that forces the sampler to move between models of different dimension. We skip that step. We expand the regression function in a **large, fixed** number of basis functions, J_n ≍ n^b (Fourier or B-splines), and let a **Horseshoe prior** on the coefficients decide which terms matter. With the basis fixed, the posterior is that of an ordinary Bayesian linear regression, so any Horseshoe sampler can fit it.

On the theory side, Theorem 1 gives posterior contraction for product shrinkage priors under prior-mass conditions adapted from Wei and Ghosal (2020). Corollary 1 turns this into adaptive, near-minimax rates over anisotropic Hölder-type classes, using one prior fixed in advance. The rate is driven mainly by how sparsely the basis represents the true function.

![Horseshoe fits to monthly sunspots, daily bike rentals and ocean wave heights](applications/reference_outputs/applications_fig.png)

*Figure 2 of the paper: posterior means (navy) and 95% bands for the three real-data examples, all fitted with the same rules.*

## What's here

| Folder | In the paper | How to run | Time |
|---|---|---|---|
| [`simulations/benchmarks/`](simulations/benchmarks) | §3.1: Figure 1, Table 1 | `Rscript run_all.R`, then `Rscript trend_plots.R` | 30–60 min per function |
| [`simulations/scaling/`](simulations/scaling) | §3.2: Table 2 | SLURM arrays, then `Rscript table2_slopes.R` | 15,500 cluster tasks |
| [`applications/`](applications) | §3.3: Figure 2 | `code/prep_*.R`, `run_applications.R`, `make_figure.R` | about 45 min |
| [`paper/`](paper) | Appendix: proofs of all lemmas | read `lemma_proofs.pdf` | |
| [`lean/`](lean) | Theorem 1, Corollary 1, Appendix D | `lake build`, then `lake env lean AxiomCheck.lean` | about 15 min with the Mathlib cache |

Each folder has its own README with the settings, the commands and the outputs. Every R script runs from its own folder and writes next to itself, so nothing needs editing.

Each folder also ships the outputs of the paper run, so you can compare without rerunning:

- Redrawing Figure 1 from the shipped results gives a byte-identical image, and all 54 entries of Table 1 match.
- Rerunning the buoy example reproduces its shipped fit byte for byte.
- The Lean build has no `sorry` and uses only Lean's three standard axioms.

## Requirements

**R.** The paper runs used R 4.4.1 with [`horseshoe`](https://CRAN.R-project.org/package=horseshoe) 0.2.0 for every MCMC fit, `ggplot2` for the figures and `digest` for the data checksums. `splines` ships with R. The cluster runs used R 4.5.2.

**Lean.** Install [elan](https://github.com/leanprover/elan). It fetches the pinned toolchain and Mathlib for you.

## Data

The three applications use public data:

- **NOAA buoy files** are included.
- **SILSO sunspots** and the **UCI bike-sharing data** are downloaded by the prep scripts and checked against the hashes from the paper's run.

Sources and citations are in [`applications/README.md`](applications/README.md).

## Citation and license

`CITATION.cff` has the reference; GitHub shows it under "Cite this repository". The code and Lean sources are MIT-licensed (see [`LICENSE`](LICENSE)). The third-party data stay under their providers' terms.

Questions or problems? Please open an issue.
