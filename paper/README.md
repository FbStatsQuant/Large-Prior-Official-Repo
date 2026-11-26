# The paper

*Large series priors for adaptive and optimal Bayesian nonparametric regression*

This folder has the LaTeX source of the paper and a compiled copy, [`large_series_priors.pdf`](large_series_priors.pdf).

```
paper/
├── large_series_priors.pdf      compiled paper (75 pages)
└── Overleaf/
    ├── main.tex                 preamble and the list of inputs
    ├── refs.bib                 bibliography (natbib, plainnat)
    ├── sections/                title and abstract, introduction, the large series prior,
    │                            numerical illustrations, conclusion, appendix overview
    ├── appendix/
    │   ├── A_proof_theorem1.tex          A  Proof of Theorem 1
    │   ├── B_proof_corollary1.tex        B  Proof of Corollary 1
    │   ├── C_admissible_ranges.tex       C  Admissible smoothness ranges for fixed dictionary exponents
    │   ├── D_approximation_lemmas.tex    D  Sparse approximation lemmas (B-spline, Fourier, Chebyshev)
    │   └── E_computation.tex             E  Exact Gibbs sampling for fixed dictionaries
    ├── recovery/coef_recovery.pdf        Figure 1
    ├── benchmark/hs_fits.pdf             Figure 2
    ├── convergence/scaling_f1.pdf        Figure 3, panel (a)
    ├── convergence/scaling_f2.pdf        Figure 3, panel (b)
    └── applications_fig.png              Figure 4
```

Each figure is produced by a folder of this repository:

| Figure | Section | Code |
|---|---|---|
| 1 (`recovery/coef_recovery.pdf`) | 3.1 | [`../simulations/recovery`](../simulations/recovery) |
| 2 (`benchmark/hs_fits.pdf`) | 3.2 | [`../simulations/benchmarks`](../simulations/benchmarks) |
| 3 (`convergence/scaling_f1.pdf`, `scaling_f2.pdf`) | 3.3 | [`../simulations/scaling`](../simulations/scaling) |
| 4 (`applications_fig.png`) | 3.4 | [`../applications`](../applications) |

## Compile

```sh
cd Overleaf
latexmk -pdf main.tex
```

This runs pdfLaTeX and BibTeX (bibliography style `plainnat`). A full TeX Live installation is enough.

The shipped PDF was built with TeX Live 2020 (pdfTeX 1.40.21). `main.tex` loads five packages that the text never uses (`dsfont`, `siunitx`, `accents`, `physics`, `tcolorbox`); they were not installed on the build machine, so they were replaced by empty stub files for that build. With a full TeX Live nothing needs to be stubbed. The build has no LaTeX warnings, undefined references or overfull boxes.

## Where the proofs are

The appendix has the full proofs of Theorem 1, Corollary 1 and every lemma they use; there is no separate companion document. Theorem 1, Corollary 1 and the sparse approximation lemmas are also machine-checked in Lean 4; see [`../lean`](../lean).

## Background literature

The proofs build most directly on these five papers. They are not redistributed here.

- Ghosal, S., Ghosh, J. K. and van der Vaart, A. W. (2000). Convergence rates of posterior distributions. *Annals of Statistics* 28(2), 500–531. [doi:10.1214/aos/1016218228](https://doi.org/10.1214/aos/1016218228)
- Ghosal, S. and van der Vaart, A. W. (2007). Convergence rates of posterior distributions for noniid observations. *Annals of Statistics* 35(1), 192–223. [doi:10.1214/009053606000001172](https://doi.org/10.1214/009053606000001172)
- Shen, W. and Ghosal, S. (2015). Adaptive Bayesian procedures using random series priors. *Scandinavian Journal of Statistics* 42(4), 1194–1213.
- Song, Q. and Liang, F. (2023). Nearly optimal Bayesian shrinkage for high-dimensional regression. *Science China Mathematics* 66(2), 409–442. [doi:10.1007/s11425-020-1912-6](https://doi.org/10.1007/s11425-020-1912-6)
- Wei, R. and Ghosal, S. (2020). Contraction properties of shrinkage priors in logistic regression. *Journal of Statistical Planning and Inference* 207, 215–229. [doi:10.1016/j.jspi.2019.12.004](https://doi.org/10.1016/j.jspi.2019.12.004)
