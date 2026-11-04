# How to compile and check the Lean proof (no Lean knowledge needed)

The Lean project is the `lean/` folder of this repository. It uses Lean `v4.35.0-rc2` (installed automatically by elan from `lean-toolchain`) and Mathlib `v4.35.0-rc2`, which Lake fetches into `.lake/packages` at the commits pinned in `lake-manifest.json`. (The author's original build used a shared local Mathlib through a `packagesDir` setting; that setting has been removed from this copy.)

## 1. Build everything

Install elan (https://github.com/leanprover/elan), then open a terminal and run:

```
cd lean
lake exe cache get   # downloads prebuilt Mathlib files; without it Mathlib compiles from source (hours)
lake build
```

Expected: after about 15 minutes from scratch (seconds if nothing changed) the last line is `Build completed successfully (8978 jobs).` (about 8978 jobs; the count changes by a few when a module is added) and no line contains `error` or `warning`. A `declaration uses 'sorry'` warning would mean an unfinished proof; there are none.

## 2. Check that the main results are what they claim and rely on no extra assumptions

```
lake env lean AxiomCheck.lean
```

Expected: 34 lines of the form `'LargePrior.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]`. These three are the standard axioms of Lean's mathematics library. Any other entry (in particular `sorryAx`) would mean something is unproved. The file also contains lines such as `example : AsymptoticStatement := asymptotic_theorem`; if they compile, the theorem has exactly the type written in `Spec.lean`, i.e. exactly the statement described in `STATEMENTS.md`.

## 3. What to read

(Paths below are relative to the repository's `lean/` folder.)

- `docs/theorem1/STATEMENTS.md`: what every Lean definition and theorem says, in plain mathematics.
- `docs/theorem1/ASSUMPTIONS.md`: modelling decisions and the places where the sources needed a repair.
- `docs/theorem1/LargePrior_blueprint.pdf`: the paper proof the Lean code follows, with the Lean name of every result.
- `LargePrior/Spec.lean`: the definitions and the main statements themselves (Theorem 1).
- For Corollary 1 and the approximation lemmas (added 2026-10-14): `docs/corollary1/STATEMENTS.md`, `docs/corollary1/ASSUMPTIONS.md`, `docs/corollary1/Corollary1_blueprint.pdf`, and `LargePrior/CorSpec.lean`.

## 4. Main results (Lean name : statement)

| Lean theorem | Statement (`Spec.lean`) |
|---|---|
| `master_theorem` | `MasterStatement` (Theorem 1 at a fixed n) |
| `asymptotic_theorem` | `AsymptoticStatement` (Theorem 1 as in the paper) |
| `main_horseshoe` | `MainHorseshoeStatement` (Theorem 1 for the horseshoe prior) |
| `horseshoe_isProbDensity` | `HorseshoeDensityStatement` |
| `horseshoe_assumption3` | `HorseshoeAssumption3Statement` ((WG3)–(WG5) for the horseshoe) |
| `fourier_basis` | `FourierBasisStatement` (Assumption 1, Fourier) |
| `bspline_basis` | `BSplineBasisStatement` (Assumption 1, B-splines) |
| `nonvacuity` | the hypotheses hold for a concrete example |
| `corollary_main` | `CorollaryStatement` (Corollary 1, given the approximation profile) |
| `cor_horseshoe` | `CorHorseshoeStatement` (Corollary 1, horseshoe prior) |
| `fourier_profile` | `FourierProfileStatement` (Fourier approximation lemma; Jackson assumed) |
| `bspline_profile`, `bspline_profile_cube` | `BSplineProfileStatement`, `BSplineProfileCubeStatement` (B-spline lemma) |
| `cor_fourier`, `cor_bspline`, `cor_bspline_cube` | end-to-end Corollary 1 for the Fourier and B-spline dictionaries |
| `cor_holder` | `CorHolderStatement` (Corollary 1 for every C^α([0,1]) function, 0 < α ≤ 1, no assumed input) |
| `corHyp_nonvacuity`, `corHorseshoe_nonvacuity`, `corFourier_nonvacuity`, `corBSpline_instance_conclusion`, `corHolder_id_conclusion`, `jackson_lip`, `corFourier_instance_conclusion` | the corollary's hypotheses hold for concrete examples |
| `cor_asymptoticHyp` | `CorTheorem1InputsStatement` (the corollary's hypotheses give the hypotheses of Theorem 1) |
| `wg4_of_card_eq` | (WG4) for one set of size a_n holds for every set of that size (`WG4Perm.lean`) |
| `wg5_iff_noPos` | for c₅ ≥ 0 the positive part in `WG5` is immaterial (`WG5Bridge.lean`) |
| `wg5Paper_implies_wg5` | the paper's pointwise-infimum (WG5) implies the Lean a.e. `WG5` (`WG5Bridge.lean`) |
| `horseshoe_assumption3_mu` | `HorseshoeAssumption3MuStatement` ((WG3) with any μ ∈ (0, μ'') for the horseshoe) |
| `horseshoe_paper_conditions` | `HorseshoePaperConditionsStatement` (the paper's eq:hs-conditions give (WG3)–(WG5)) |
| `horseshoe_assumption3_of_mu` | `HorseshoeAssumption3Statement` as the μ = μ''/2 instance of `HorseshoeAssumption3MuStatement` |
