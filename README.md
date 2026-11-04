# Large series priors for adaptive and optimal Bayesian nonparametric regression

Code and machine-checked proofs for the paper by **Felipe Bedoya** and **Meng Li** (Department of Statistics, Rice University).

> Random series priors are widely used in nonparametric Bayesian regression, and their performance depends critically on the number of basis functions. A fixed truncation level is simple but must be matched to the unknown smoothness, while hierarchical priors on the number of terms are adaptive but require sampling over spaces of varying dimension. We propose a large series prior: a deterministic number of basis functions growing as n^b for a constant b > 0, where n is the sample size, combined with a shrinkage prior on the coefficients. We establish posterior contraction rates for product shrinkage priors satisfying prior-mass conditions, with general dictionaries. For anisotropic Hölder-type classes and Fourier or multiresolution B-spline dictionaries, one prior, fixed in advance, attains near-minimax rates pointwise over the range of smoothness allowed by the dictionary; the Horseshoe with a deterministic global scale satisfies the required conditions. Posterior computation is that of a linear regression of fixed dimension under a shrinkage prior, so standard samplers apply. Simulations and three real-data applications illustrate the method.

## How to cite

```
Bedoya, F. and Li, M. Large series priors for adaptive and optimal Bayesian
nonparametric regression.
```

A `CITATION.cff` file is included (GitHub shows it under "Cite this repository"). Journal and preprint identifiers will be added when available.

## Contents

| Folder | Paper | Language |
|---|---|---|
| `simulations/benchmarks_ridge_hs/` | Section 3.1: Figure 1, Table 1 | R |
| `data_applications/` | Section 3.3: Figure 2 and the numbers in the text | R |
| `lean/` | Theorem 1, the Horseshoe paragraph, Corollary 1, Appendix D lemmas | Lean 4 |

## What reproduces what

| Paper item | Script(s) | Expected runtime | Status |
|---|---|---|---|
| Figure 1 (Fourier/cosine estimates, n = 1000, J_n = 125) | `simulations/benchmarks_ridge_hs/run_all.R` (runs `function_{1,2,3}.R`), then `trend_plots.R` | 30–60 min per function on a laptop; `trend_plots.R` alone: seconds | Reproduced: the paper's JPG is byte-identical |
| Table 1 (MSE, J_n = 140, …, 300) | same `function_{1,2,3}.R` (write `f*_table_rows.tex`) | included above | Reproduced: all 54 entries match `reference_outputs/` |
| Table 2 (convergence study, Section 3.2) | to be added in a later update | | Code to follow |
| Figure 2 and Section 3.3 numbers | `data_applications/code/prep_{sunspots,bike,buoy}.R`, `run_applications.R`, `make_figure.R` | sunspots ≈ 30 min; bike, buoy ≈ 6 min each | Reproduced: prepared data, fits and figure match byte for byte |
| Theorem 1, Horseshoe paragraph, Corollary 1 | `lean/` | full build ≈ 15 min after `lake exe cache get` | Machine-checked (see below) |

To redraw Figure 1 without rerunning the MCMC, copy `simulations/benchmarks_ridge_hs/reference_outputs/` to `results/` and run `Rscript trend_plots.R`.

### Table 2

The code for the convergence study of Section 3.2 (Table 2) will be added in a later update.

## Requirements

**R.** The paper runs used R 4.4.1.

| Package | Used by | Version |
|---|---|---|
| horseshoe | all MCMC | 0.2.0 (recorded in `sessionInfo` and the run summaries) |
| ggplot2 | figures | 4.0.2 (recorded in `sessionInfo`) |
| splines, grid | B-spline basis, `make_figure.R` | ship with R |
| digest | `data_applications/` checksums | 0.6.39 (installed; not recorded at run time) |

The full `sessionInfo()` of the Figure 1 and Table 1 runs is in `simulations/benchmarks_ridge_hs/reference_outputs/function_*/f*_summary.txt`.

**Lean.** [elan](https://github.com/leanprover/elan), which installs the toolchain in `lean/lean-toolchain` (`leanprover/lean4:v4.35.0-rc2`); Mathlib `v4.35.0-rc2` is pinned in `lean/lake-manifest.json`.

## How to run

### Figure 1 and Table 1

```
cd simulations/benchmarks_ridge_hs
Rscript run_all.R            # writes results/function_{1,2,3}/
Rscript trend_plots.R        # writes trend_plots/ (Figure 1)
Rscript run_all.R --quick    # fast check, not the paper settings
```

Settings: n = 1000; σ = 0.15, 0.07, 0.10 for f1, f2, f3; seed 1991; half-Cauchy global scale; burn 1000, nmc 5000; ridge with 20-fold CV over 160 penalty values. See `simulations/benchmarks_ridge_hs/README.md`.

### Figure 2

```
cd data_applications
Rscript code/prep_buoy.R        # raw NOAA files are included and checked against SHA256SUMS.txt
Rscript code/prep_sunspots.R    # downloads from SILSO, then checks SHA256SUMS.txt
Rscript code/prep_bike.R        # downloads from UCI, then checks SHA256SUMS.txt
Rscript code/run_applications.R # writes output/<name>_fit.csv and _summary.txt
Rscript code/make_figure.R      # writes output/applications_fig.{png,pdf}
```

SILSO updates its file monthly, so a fresh download usually differs from the paper's; `prep_sunspots.R --refresh` accepts the current file (the paper's prepared series has sha256 `bdfb32d712d9d244c93f6c4341274f3ffe377e374b0d0570aab5909df7d1eccb`). The model is specified in `data_applications/METHODS_SPEC.md` (F_n = floor(n^0.7) frequencies; τ = F_n^-2; Jeffreys prior on σ; burn 10000, nmc 20000; seed 20261027).

## Lean formalization

`lean/` is one Lake package, `LargePrior`. Every result below is proved in Lean 4 with Mathlib; the only axioms used are Lean's three standard ones. The classical approximation results used by the Appendix D lemmas (the Jackson–Stechkin inequality, B-spline stability and one-block spline approximation) enter as explicit hypotheses of those statements, never as axioms.

**Build and check.**

```
cd lean
lake exe cache get              # prebuilt Mathlib (without it, Mathlib compiles for hours)
lake build                      # about 15 minutes; ends "Build completed successfully"
lake env lean AxiomCheck.lean   # every line: depends on axioms: [propext, Classical.choice, Quot.sound]
```

`AxiomCheck.lean` also contains lines `example : <Statement> := <theorem>`; they compile only if each theorem has exactly the stated type.

**Headline results** (definitions and statements in `lean/LargePrior/Spec.lean`, `CorSpec.lean`, `HorseshoePaper.lean`).

| Paper | Lean statement (theorem) | What it says |
|---|---|---|
| Theorem 1 | `AsymptoticStatement` (`asymptotic_theorem`) | Under Assumptions 1–3 and the standing requirements, for every M_n → ∞: E₀Π(‖f − f₀‖_{2,n} > M_n ε_n \| Y) ≤ 5e^{−nε̃²} (the paper states 6), E₀Π(#{j : \|θ_j\| > δ_n} > A s_n \| Y) ≤ 2e^{−nε̃²} for an explicit integer A depending only on (K, σ, μ, η, c₄, c₅), and both posterior probabilities → 0 in P₀-probability |
| Theorem 1, fixed n | `MasterStatement` (`master_theorem`) | the same bounds at a single n under explicit numerical conditions |
| Horseshoe paragraph (Section 2) | `HorseshoePaperConditionsStatement` (`horseshoe_paper_conditions`) | the conditions eq:hs-conditions imply Assumption 3 for the Horseshoe, with any μ < μ′ in (WG3) |
| Horseshoe, Wei–Ghosal bounds | `HorseshoeAssumption3MuStatement` (`horseshoe_assumption3_mu`), `MainHorseshoeStatement` (`main_horseshoe`) | (WG3)–(WG5) for the Horseshoe with deterministic scale; Theorem 1 for the Horseshoe |
| Assumption 1 for the dictionaries | `FourierBasisStatement`, `BSplineBasisStatement` | K = 2^{d/2} (Fourier), K = 1 (B-splines) |
| Corollary 1 | `CorollaryStatement` (`corollary_main`) | given the sparse approximation profile: Assumption 2 and the standing requirements hold so that Theorem 1 applies (`cor_asymptoticHyp`), (i) s_n ≍ a_n ≍ (n/log n)^{d/(2α*+d)} and ε_n ≍ ρ_n, (ii) the two bounds with the explicit constants A′ = A C_s/C_sp and c = C_ε²/C_a of Appendix B, (iii) convergence in P₀-probability |
| Corollary 1, Horseshoe | `CorHorseshoeStatement` (`cor_horseshoe`) | Corollary 1 for the Horseshoe with τ_n = J_n^{−(2+μ′)}/√n, Assumption 3 derived |
| Corollary 1, end to end | `CorFourierStatement`, `CorBSplineStatement`, `CorBSplineCubeStatement`, `CorHolderStatement` | Corollary 1 for the Fourier and multiresolution B-spline dictionaries (classical inputs as hypotheses); `CorHolderStatement` needs no assumed input |
| Appendix D lemmas | `FourierProfileStatement`, `BSplineProfileStatement`, `BSplineProfileCubeStatement` | the sparse approximation profiles |

Documented differences from the paper, all on the safe side (Lean proves at least what the paper states): the constant 5 instead of 6; assumptions required only for large n; (WG5) in an almost-everywhere form implied by the paper's (the Lean Horseshoe density takes the value 0 at the single point t = 0, where the paper's is +∞). Plain-mathematics descriptions of every statement are in `lean/docs/theorem1/STATEMENTS.md` and `lean/docs/corollary1/STATEMENTS.md`; the blueprints `lean/docs/*/*_blueprint.pdf` follow the paper's proofs step by step.

## Data

| Data set | Source | Included |
|---|---|---|
| NOAA NDBC buoy 46001, standard meteorological data 2010–2023 | https://www.ndbc.noaa.gov/data/historical/stdmet/46001hYYYY.txt.gz | Yes (raw files and `data/buoy.csv`); US Government data, public domain |
| SILSO monthly and daily total sunspot number V2.0 (Royal Observatory of Belgium) | https://www.sidc.be/SILSO/INFO/snmtotcsv.php, https://www.sidc.be/SILSO/INFO/sndtotcsv.php | No; downloaded by `prep_sunspots.R`. Cite SILSO (doi:10.24414/qnza-ac80) and Clette et al. (2014) |
| Capital Bikeshare daily rentals 2011–2012 (UCI "Bike Sharing") | https://archive.ics.uci.edu/static/public/275/bike%2Bsharing%2Bdataset.zip | No; downloaded by `prep_bike.R`. Cite Fanaee-T and Gama (2014), doi:10.24432/C5W894 |

The data are distributed under their providers' terms, which this repository's license does not change.

## License

MIT; see `LICENSE`. The license covers the code and the Lean sources in this repository, not the third-party data.
