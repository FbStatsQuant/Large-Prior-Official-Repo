# Lean formalization

*Theorem 1 · Corollary 1 · the sparse approximation lemmas*

This folder contains machine-checked proofs, in Lean 4 with Mathlib, of the paper's main theoretical results:

- **Theorem 1**: posterior contraction for product shrinkage priors under Assumptions 1–3.
- **The Horseshoe paragraph** after Theorem 1: the Horseshoe with a deterministic global scale satisfies Assumption 3.
- **Corollary 1**: adaptive contraction rates from the sparse approximation profile.
- **The sparse approximation lemmas** for the three dictionaries of the paper: Fourier, B-spline and Chebyshev (tensor products of Chebyshev polynomials on [0,1]^d, for sectional Hölder classes). The classical approximation theorems they rely on enter as explicit hypotheses (see below).

Every theorem is proved: there is no `sorry`, and the only axioms are Lean's standard three (`propext`, `Classical.choice`, `Quot.sound`). The classical approximation inputs (the Jackson–Stechkin inequality, B-spline stability and the one-block spline approximation) are hypotheses of the profile lemmas and end-to-end statements, not axioms, so `#print axioms` does not list them; see "Differences from the paper" below.

## Build and check

You need [elan](https://github.com/leanprover/elan). It installs the toolchain pinned in `lean-toolchain` (`leanprover/lean4:v4.35.0-rc2`); Mathlib is pinned in `lake-manifest.json`.

```sh
cd lean
lake exe cache get              # prebuilt Mathlib; without it Mathlib compiles for hours
lake build                      # ~15 min; ends with "Build completed successfully"
lake env lean AxiomCheck.lean   # prints the axioms each main theorem uses
```

[`AxiomCheck.lean`](AxiomCheck.lean) does two things:

- Lines like `example : AsymptoticStatement := asymptotic_theorem` compile only if the theorem has exactly the stated type.
- The `#print axioms` lines should all read `[propext, Classical.choice, Quot.sound]`.

`SHA256SUMS.txt` lists the hashes of the Lean sources, so you can confirm they are the ones we checked (`sha256sum -c SHA256SUMS.txt`).

## Where the statements are

| Paper | Lean statement | Proved by |
|---|---|---|
| Theorem 1 | `AsymptoticStatement` | `asymptotic_theorem` |
| Theorem 1 at a fixed n, with explicit conditions | `MasterStatement` | `master_theorem` |
| Horseshoe paragraph after Theorem 1 (its conditions ⇒ Assumption 3) | `HorseshoePaperConditionsStatement` | `horseshoe_paper_conditions` |
| Theorem 1 for the Horseshoe | `MainHorseshoeStatement` | `main_horseshoe` |
| Assumption 1 for Fourier / B-spline atoms | `FourierBasisStatement`, `BSplineBasisStatement` | `fourier_basis`, `bspline_basis` |
| Corollary 1 | `CorollaryStatement` | `corollary_main` |
| Corollary 1 for the Horseshoe | `CorHorseshoeStatement` | `cor_horseshoe` |
| Fourier profile lemma | `FourierProfileStatement` | `fourier_profile` |
| B-spline profile lemma | `BSplineProfileStatement`, `BSplineProfileCubeStatement` | `bspline_profile`, `bspline_profile_cube` |
| Corollary 1 end to end: periodic Hölder–Zygmund f₀, Fourier | `CorFourierStatement` | `cor_fourier` |
| Corollary 1 end to end: multiresolution B-splines | `CorBSplineStatement` | `cor_bspline` |
| Corollary 1 end to end: B-splines, isotropic | `CorBSplineCubeStatement` | `cor_bspline_cube` |
| Corollary 1 end to end: C^α([0,1]), 0 < α ≤ 1, nothing assumed | `CorHolderStatement` | `cor_holder` |
| Assumption 1 for Chebyshev atoms | `ChebyshevBasisStatement` | `chebyshev_basis` |
| Smoothness transfer under the Chebyshev fold | `ChebTransferStatement` | `cheb_transfer_statement` |
| Chebyshev profile lemma, univariate and sectional anisotropic | `ChebyshevProfileStatement`, `ChebyshevAnisoProfileStatement` | `chebyshev_profile`, `chebyshev_aniso_profile` |
| Chebyshev profile at a design (the input of Corollary 1) | `ChebyshevProfileAtStatement` | `chebyshev_profile_at` |
| Corollary 1 end to end: sectional Hölder f₀, Chebyshev | `CorChebyshevStatement`, `CorChebyshevExStatement` | `cor_chebyshev`, `cor_chebyshev_ex` |
| Corollary 1 end to end: Chebyshev, α ∈ (0,1)^d, nothing assumed | `CorChebyshevHolderStatement` | `cor_chebyshev_holder` |

The statements are collected in [`LargePrior/Spec.lean`](LargePrior/Spec.lean), [`LargePrior/CorSpec.lean`](LargePrior/CorSpec.lean), [`LargePrior/HorseshoePaper.lean`](LargePrior/HorseshoePaper.lean) and [`LargePrior/ChebSpec.lean`](LargePrior/ChebSpec.lean). [`docs/statements.md`](docs/statements.md) explains each one in plain mathematics, so you can compare it with the paper without reading Lean.

## Differences from the paper

**Theorem 1** has the paper's hypotheses and conclusions, with some small differences that all point the safe way:

- The first bound has the constant 5 where the paper states 6.
- Every condition on the sequences is required only for large n.
- (WG5) is stated with an almost-everywhere lower bound on the density. The paper's pointwise version implies it (`wg5Paper_implies_wg5`), and this form is needed for the Horseshoe, whose density is infinite at 0.

**Corollary 1** has the paper's hypotheses and conclusions, including the explicit constants A′ = A C_s/C_sp and c = C_ε²/C_s from the proof of Corollary 1 in the Appendix. The differences point the same safe way: the constant 5 in place of 6 in the first bound of (ii), and the profile required only for large n.

**The classical approximation inputs** are hypotheses of the profile lemmas and the end-to-end statements: the Jackson–Stechkin inequality, B-spline stability, and the one-block spline approximation of Hölder functions. Each is proved in Lean for a base case:

- Jackson for 0 < α < 1;
- B-spline stability for order 1;
- spline approximation for univariate C^α with α ≤ 1.

As a result, `CorHolderStatement`, which is Corollary 1 for every f₀ in a C^α([0,1]) ball with 0 < α ≤ 1, has no assumed input at all.

**The Chebyshev dictionary** inherits the Corollary 1 differences above. The profile lemmas, `CorChebyshevStatement` and `CorChebyshevHolderStatement` keep the paper's displayed constants: C_sp = 1, E = R and, in the corollaries, any C_ε ≥ d·C_app, with C_app written out. Those two corollaries hold for any sizes L_{n,k} ≍ n^{b_k} and any enumeration of the atoms. The convenience form `CorChebyshevExStatement` has existential constants and the ceiling sizes ⌈n^{b_k}⌉. The smoothness transfer under the fold is proved for every α > 0. The Jackson inequality is the only classical input. It is proved for 0 < α < 1, so `CorChebyshevHolderStatement`, which is Corollary 1 for α ∈ (0,1)^d in any dimension, has no assumed input. For α_k ≥ 1 the Jackson inequality stays a hypothesis. The end-to-end statements use the Horseshoe, as `cor_horseshoe` does. Not formalized: the Gauss–Chebyshev Gram identity, the arcsine-weight coefficient formulas, the inclusions between the classes, and Jackson for α ≥ 1. [`docs/statements.md`](docs/statements.md) §§10–12 has the details.

## Files

```
lean/
├── LargePrior/            the development (Spec, CorSpec, HorseshoePaper and ChebSpec hold the statements)
├── LargePrior.lean        imports every module
├── AxiomCheck.lean        type and axiom checks for the main results
├── docs/statements.md     the statements in plain mathematics
├── lakefile.toml, lake-manifest.json, lean-toolchain
└── SHA256SUMS.txt
```

A rough map of `LargePrior/`. Every file opens with a short description.

| Part | Modules |
|---|---|
| Statements | `Spec`, `CorSpec`, `HorseshoePaper`, `ChebSpec` |
| Theorem 1 | `Basic`, `Gaussian`, `Posterior`, `LocalMass`, `Evidence`, `Sieve`, `BasicTest`, `Packing`, `Covering`, `Tests`, `Master`, `Asymptotic`, `WG4Perm`, `WG5Bridge` |
| Horseshoe | `Horseshoe`, `WGFixed`, `HorseshoeAsymptotic`, `HorseshoeMain` |
| Dictionaries | `Basis`, `BSpline` |
| Corollary 1 | `CorSeqA`, `CorSeq`, `Corollary`, `CorHorseshoe`, `EndSizes`, `EndToEnd` |
| Fourier profile | `TrigBasics`, `Fejer`, `VdPBasics`, `VdP` (de la Vallée Poussin), `FourierTensor`, `FourierExpand`, `FourierProfile`, `Jackson` |
| B-spline profile | `SplineBook`, `SplineReadout`, `SplinePad`, `SplineProfile` |
| Chebyshev | `ChebBasis`, `ChebTransfer`, `ChebTransferHigh`, `ChebTensor`, `ChebProfile`, `ChebEndToEnd`, `ChebMain` |
| Checks | `NonVacuity`, `CorNonVacuity`, `CorNonVacuityS`, `Sanity`, `CorSanity`, `ChebChecks` |
