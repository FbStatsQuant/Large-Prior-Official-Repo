# STATEMENTS — Corollary 1 and the sparse approximation lemmas, in plain mathematics

Lean file: `lean/LargePrior/CorSpec.lean`. It builds on Theorem 1 (`Spec.lean`, frozen v2; see `docs/theorem1/STATEMENTS.md`). Repairs (G) and decisions (D) are in `ASSUMPTIONS.md`. Read this file to check that the Lean statements say what the paper says, after the repairs. No Lean knowledge is needed.

**Status (2026-10-14, end of Phase 2): every statement below is proved in Lean**, with no `sorry`, and depends only on the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The classical inputs of §2 remain assumptions where they appear as hypotheses.

**Updated 2026-11-03 (frozen `cor_v2`):** §3 now states the explicit constants A′ and c and exports "Theorem 1 applies" as a conjunct; (WG4) is assumed for one set only. The change list is in `ASSUMPTIONS.md`.

## 1. Objects

| Lean | Meaning |
|---|---|
| `alphaStar α`, `rateExp α`, `dimExp α`, `betaExp α k` | α* = d / Σ_k α_k⁻¹; r = α*/(2α* + d); D = d/(2α* + d); β_k = α*/(α_k(2α* + d)). |
| `corN n J` | N_n = n / log J_n. |
| `corM α n J k` | m_{n,k} = ⌈N_n^{β_k}⌉ (balanced budget, of order (n/log n)^{β_k}; G11). |
| `corA Csp α n J` | a_n = ⌈C_sp ∏_k m_{n,k}⌉. |
| `corEpsT Ceps α n J` | ε̃_n = C_ε N_n^{−r}. |
| `corDelta cδ Ceps α n J` | δ_n = c_δ ε̃_n / J_n. E_n = E (a constant). |
| `corRate α n` | (n / log n)^{−r}. |
| `suppCard θ` | #{j : θ_j ≠ 0}. |
| `ProfileAt X f₀ L α Csp Capp E` | The sparse approximation profile (eq:aniso-profile) at one n: for every integer rectangle 1 ≤ m_k ≤ L_k (G10), some θ has #supp θ ≤ C_sp ∏ m_k, ‖f₀ − f_θ‖_{2,n} ≤ C_app Σ_k m_k^{−α_k}, and max_j \|θ_j\| ≤ E. |
| `SizesComparable b L J` | L_{n,k} ≍ n^{b_k} and J_n ≍ ∏_k L_{n,k}: for some constants c > 0 and C, and all large n, c n^{b_k} ≤ L_{n,k} ≤ C n^{b_k} and c ∏ L ≤ J ≤ C ∏ L. |
| `corTau μ'' n J` | Horseshoe global scale τ_n = J_n^{−(2+μ'')} / √n (D11). |
| `fdiff r h g x` | Δ_h^r g(x) = Σ_{v=0}^{r} (−1)^{r−v} C(r,v) g(x + vh). |
| `sectionAt f x k` | t ↦ f(x₁, …, x_{k−1}, t, x_{k+1}, …, x_d). |
| `HZBall1 α r R g` | g: ℝ → ℝ continuous, 1-periodic, and ‖g‖_∞ + sup_{0<\|h\|≤1/2} \|h\|^{−α} ‖Δ_h^r g‖_∞ ≤ R (written as bounds A + B ≤ R; D7). |
| `HZBall α r R f` | f: ℝ^d → ℝ continuous, 1-periodic in every coordinate, and ‖f‖_∞ + max_k sup_{0<\|h\|≤1/2} \|h\|^{−α_k} ‖Δ_{he_k}^{r_k} f‖_∞ ≤ R. This is the coordinatewise periodic anisotropic Hölder–Zygmund ball of Appendix D (G5, G9). |
| `HolderBall1 α R f` | \|f\| ≤ R and \|f(x) − f(y)\| ≤ R \|x − y\|^α on [0,1]: the C^α([0,1]) ball for 0 < α ≤ 1 (Lipschitz at α = 1, the manuscript's convention C¹ = C^{0,1}). |
| `IsTrigPoly q p` | p = Σ_{ν=0}^{2q} c_ν ψ_ν: a real trigonometric polynomial of degree ≤ q. |
| `FourierIdx M`, `fourierSeries θ` | The tensor Fourier dictionary F_M, with ν_k ∈ {0, …, 2M_k} and atoms Ψ_ν = ∏_k ψ_{ν_k}(x_k), where ψ₀ = 1, ψ_{2j−1} = √2 cos 2πjx, ψ_{2j} = √2 sin 2πjx. f_θ = Σ_ν θ_ν Ψ_ν. |
| `splineDim q ℓ`, `splineUnionDim q H` | D_ℓ = 2^ℓ + q − 1; U_H = Σ_{ℓ=0}^{H} D_ℓ. |
| `SplineIdx q H`, `splineAtom`, `splineSeries θ` | The tagged multiresolution tensor dictionary D_H^{(q)}. In coordinate k an index is a level ℓ ≤ H_k and a position i < D_ℓ. The atom is ∏_k B_{ℓ_k,i_k}(x_k), with B_{ℓ,i} the order-q B-spline on 2^ℓ equal subintervals with clamped knots (the Theorem 1 package's `bspline`). |
| `blockSeries q ℓ θ` | A one-block tensor spline at levels (ℓ_1, …, ℓ_d): Σ_j θ_j ∏_k B_{ℓ_k,j_k}(x_k). |
| `unitCube d` | [0,1]^d. |
| `fourierM b n k`, `fourierJ`, `fourierX` | Fourier sizes M_{n,k} = ⌈n^{b_k}⌉; J_n = ∏_k(2M_{n,k} + 1); the n × J_n design matrix at the design points (columns enumerated by a fixed bijection; D10). |
| `splineH b n k`, `splineJ`, `splineX` | Spline truncation H_{n,k} = ⌈b_k log₂ n⌉; J_n = ∏_k U_{H_{n,k}}; the design matrix. |

Assumption 3's (WG5) is Theorem 1's form: a positive lower bound on the density holding **almost everywhere** on [−E, E]. It is implied by the manuscript's pointwise infimum, and it is insensitive to changing the density on a null set. This matters for the horseshoe, whose Lean density is 0 at the single point t = 0.

## 2. Classical inputs (assumed; D1)

Each of these is a hypothesis of the statements that use it. If one were stated wrongly (false), the statements using it would be vacuous. That is why each is listed with its source, for review.

- **`JacksonIneq α r C`** (periodic Jackson inequality): for every R, every g in `HZBall1 α r R`, and every q ≥ 1, some trigonometric polynomial p of degree ≤ q has sup_x \|g(x) − p(x)\| ≤ C R q^{−α}.
  - Source: the Jackson–Stechkin theorem E_q(g) ≤ C_r ω_r(g, 1/q), cited in the paper as Temlyakov 2018. The exact theorem number is unverified.
  - **Proved for 0 < α < 1 and r = 1** (`jackson_lip`, constant C = 2 + 1/(2(1 − α))). For other (α, r) it remains assumed.
- **`BSplineReadout q C_dual`** (B-spline stability): for every level ℓ and every univariate spline s = Σ_i θ_i B_{ℓ,i}, max_j \|θ_j\| ≤ C_dual sup_{[0,1]} \|s\|.
  - Source: Schumaker Thm 4.41 / de Boor, as cited in the paper (unverified).
  - **Proved for q = 1** (`bsplineReadout_one`, C_dual = 1). For q = 2, 3, 4 attack A2 ran finite numerical checks with the Lean B-spline conventions; these are evidence, not a proof.
- **`SplineOneBlock q α C⋆ f₀`** (applied to f₀): for every level vector (ℓ_1, …, ℓ_d), some one-block spline is within C⋆ Σ_k D_{ℓ_k}^{−α_k} of f₀ on [0,1]^d.
  - Sources (G8): Schumaker Thm 6.10 for d = 1, 0 < α ≤ q, and f₀ in a C^α([0,1]) ball. Schumaker Thm 12.7 via Shen–Ghosal (2015) Lemma 2(a) for integer α_k ≤ q and f₀ in a ball of the anisotropic mixed-derivative class of Appendix D.
  - **Proved for q = 1, d = 1, 0 < α ≤ 1 and f₀ in `HolderBall1`** (`splineOneBlock_holder`, C⋆ = R; §5b).
- **`SplineOneBlockCube d q α C⋆ f₀`**: the same at common levels ℓ, with error C⋆ D_ℓ^{−α}.
  - Source: Shen–Ghosal (2015) Remark 7, for 0 < α ≤ q and f₀ in a C^α([0,1]^d) ball (stated there without proof; G8).

The spline Hölder classes for α > 1, for d ≥ 2, and the anisotropic class are not defined in Lean (D1). For those, the spline statements read "for every f₀ satisfying the one-block approximation property", which the cited theorems give for f₀ in the class.

## 3. Corollary 1 (abstract form)

**`CorollaryStatement` = `CorHyp` ⇒ `CorConclusion`.**

*Hypotheses (`CorHyp`):*
- d ≥ 1 and α_k > 0 fixed; b_k ≥ β_k; `SizesComparable b L J`.
- σ > 0; Assumption 1 with a fixed K > 0, for large n.
- The profile `ProfileAt` with fixed C_sp > 0, C_app ≥ 0, E > 0, for all large n (D3).
- C_ε > 0 with C_ε ≥ d·C_app (D4), and c_δ ∈ (0,1).
- Assumption 3 for the sequences of §1, for large n:
  - π_n is a probability density;
  - (WG3) with δ_n and a constant μ > 0;
  - (WG4) with η ∈ (0,1) and c₄ ≥ 0, **for one set of size a_n** (`CorHyp.h4`). `wg4_of_card_eq` (`WG4Perm.lean`) transfers it to the active set ξ*_n built in the proof, by a coordinate permutation (the prior is iid). This retires the old D2;
  - (WG5) with E and c₅ ≥ 0, in the almost-everywhere form of Theorem 1 (the paper's pointwise (WG5) implies it: `wg5Paper_implies_wg5`).

*Conclusions: `CorollaryStatement` is item 0 together with `CorConclusion` (items 1 and 2), with s_n and ε_n as in Theorem 1:*
0. **Theorem 1 applies.** For every sequence M_n → ∞, `CorTheorem1Inputs` holds: these are the hypotheses of Theorem 1 (`AsymptoticHyp`) at the corollary's sequences a_n, ε̃_n, δ_n, E_n = E. So Assumption 2 (with an active set ξ*_n of exactly a_n indices and (WG4) for it) and the standing requirements hold, i.e. "Assumption 2 and the standing requirements hold, so that Theorem 1 applies". It is proved by `cor_asymptoticHyp` (`CorTheorem1InputsStatement`).
1. **Orders (G1, G2; proved, not assumed).** For some C > 0 and all large n:
   - a_n ≤ s_n ≤ C a_n;
   - C⁻¹ (n/log n)^D ≤ a_n ≤ C (n/log n)^D, **with D = d/(2α* + d)** (G1; the manuscript now prints this exponent, and its earlier remark 1/(2α* + d) is obsolete);
   - C⁻¹ (n/log n)^{−r} ≤ ε_n ≤ C (n/log n)^{−r}.
2. **Contraction, with explicit constants.** Let A = `Aconst K η σ μ c4 c5` be the integer of Theorem 1. The constants are A′ = `corAprime A d Csp Ceps` = A·C_s/C_sp > 0, a real number (not necessarily an integer), and c = `corExpConst d Csp Ceps` = C_ε²/C_a > 0, where C_a = 2^d C_sp + 1 and C_s = max{C_a, C_ε² + 1} (Appendix B, eq:cor-constants). They match the manuscript, which claims A′ and c depend only on (A, C_sp, C_ε, d). For every sequence M_n → ∞, for all large n:
   - E₀ Π(‖f_θ − f₀‖_{2,n} > M_n (n/log n)^{−r} | Y) ≤ 5 e^{−c a_n log J_n} (D5; the manuscript has 6);
   - E₀ Π(#{j : \|θ_j\| > δ_n} > A′ a_n | Y) ≤ 2 e^{−c a_n log J_n} (the threshold A′ a_n is real: `denseSetReal`);
   - for every ζ > 0, the probability that either posterior probability exceeds ζ tends to 0 under P₀.

**Not claimed:**
- A′ and c are explicit functions of (A, C_sp, C_ε, d) only, where A is the integer of Theorem 1; they do not depend on M_n. The constant C of item 1 is chosen after all the data: the dictionary sequences L, J, X, the truth f₀, the prior, and the fixed constants. This matches the manuscript, whose constants are also fixed after the setting.
- The threshold "large n" may depend on M_n.
- Nothing is uniform over α.
- The profile and the prior conditions are assumptions.
- The bounds hold eventually, not for every n.
- The standing requirements (n ε̃_n² → ∞, s_n log J_n = o(n), and ε̃_n → 0 of G3) are derived inside the proof as lemmas; they are exported only through item 0 (`CorTheorem1Inputs`), not as separate conclusions.

**`CorHorseshoeStatement`:** the same conclusions for the horseshoe prior with τ_n = J_n^{−(2+μ'')}/√n, μ'' > 0. The hypotheses are those of `CorHyp` minus Assumption 3, which is derived (G6). τ_n does not depend on α. The statement has the form ∃ c₅ ≥ 0 such that item 0 holds with (μ = μ''/2, c₄ = 1, c₅) and `CorConclusion` holds with A = `Aconst K η σ (μ''/2) 1 c5`. The choice μ = μ''/2 is one valid choice (Theorem 1's `horseshoe_assumption3_mu` allows any μ ∈ (0, μ'')); the frozen statement keeps it.

**End-to-end statements (§5, §5b)** have the same shape. First ∃ C_sp, C_ε, E (chosen before the truth, the design, the exponent and the prior constants); then, for every admissible choice, ∃ c₅ ≥ 0 such that item 0 holds (with μ = μ''/2, c₄ = 1, c₅ and K = 2^{d/2} for Fourier, K = 1 for splines) and `CorConclusion` holds with A = `Aconst K η σ (μ''/2) 1 c5`.

## 4. The approximation lemmas

**`FourierProfileStatement`** (Lemma fourier-profile, sup-norm; D6). Let d, α_k > 0 and integers r_k > α_k be given, and assume the Jackson inequality in every coordinate with constants C_J,k. Then there is C ≥ 0, depending only on (d, α, r, C_J), such that for every R, every f₀ in `HZBall α r R`, every dictionary size M, and every rectangle 1 ≤ m_k ≤ 2M_k + 1, some θ on F_M has:
- #supp θ ≤ ∏_k m_k;
- sup_{x∈ℝ^d} \|f₀(x) − f_θ(x)\| ≤ C R Σ_k m_k^{−α_k};
- \|θ_ν\| ≤ R for every ν.

**`BSplineProfileStatement`** (Lemma bspline-profile, parts 1 and 3). Let q ≥ 1, α_k > 0, C⋆ ≥ 0, C_dual ≥ 1 with `BSplineReadout q C_dual`, and R be given. There are C_sp > 0, C_app ≥ 0, E > 0, depending only on (d, q, α, C⋆, C_dual, R), such that for every truncation H, every f₀ with \|f₀\| ≤ R on [0,1]^d and `SplineOneBlock q α C⋆ f₀`, and every rectangle 1 ≤ m_k ≤ U_{H_k}, some θ on D_H^{(q)} has:
- #supp θ ≤ C_sp ∏_k m_k;
- sup_{[0,1]^d} \|f₀ − f_θ\| ≤ C_app Σ_k m_k^{−α_k};
- \|θ_ι\| ≤ E.

**`BSplineProfileCubeStatement`** (part 2, isotropic). The same with d ≥ 1, a common truncation H, scalar α, and `SplineOneBlockCube`. The error is C_app Σ_k m_k^{−α} for every rectangle, obtained via m = min_k m_k (G10).

**Not claimed:**
- The classical inputs themselves (§2), except where a proof is listed.
- For splines, anything about function classes beyond the one-block property, except `HolderBall1` with q = 1 (§5b).
- For Fourier, non-periodic f₀ (G5). Such functions are excluded; Astra's counterexample is f₀(x) = x.

## 5. End to end: Assumption 2 derived from the function class

All of these use the horseshoe prior with τ_n = J_n^{−(2+μ'')}/√n.

**Constants come first (Gate A).** In each statement, the constants C_sp and C_ε are chosen once, depending only on the fixed class parameters. They are then valid for every truth f₀ in the class, every admissible exponent b, every design, every σ > 0, η ∈ (0,1), μ'' > 0, and **every c_δ ∈ (0,1)**. The conclusion is `CorConclusion`; in particular the posterior contracts at M_n (n/log n)^{−r}.

- **`CorFourierStatement`.**
  - Classical input: the Jackson inequality in every coordinate.
  - Class parameters (fixed before the constants): d, α_k > 0, r_k > α_k, C_J, R.
  - Then for every b_k ≥ β_k, every f₀ ∈ `HZBall α r R`, and arbitrary design points, with the Fourier dictionary M_{n,k} = ⌈n^{b_k}⌉.
- **`CorBSplineStatement`.**
  - Classical input: `BSplineReadout q C_dual`.
  - Class parameters: d, q ≥ 1, α_k > 0, C⋆ ≥ 0, C_dual ≥ 1, R.
  - Then for every f₀ with `SplineOneBlock q α C⋆ f₀` and \|f₀\| ≤ R on the cube, every b_k ≥ β_k, and design points in [0,1]^d (G9), with H_{n,k} = ⌈b_k log₂ n⌉.
- **`CorBSplineCubeStatement`.** The isotropic version, with d ≥ 1, scalar α, a common exponent b ≥ 1/(2α + d) (D12), and `SplineOneBlockCube`.

### 5b. Univariate Hölder classes with no assumed input

**`CorHolderStatement`.** Fix 0 < α ≤ 1 and R ≥ 0. There are C_sp, C_ε > 0 such that, for every f₀ in `HolderBall1 α R` (the C^α([0,1]) ball), the conclusions of Corollary 1 hold for:
- every exponent b ≥ 1/(2α + 1);
- every design in [0,1];
- order-1 multiresolution B-splines with H_n = ⌈b log₂ n⌉;
- the horseshoe prior;
- every σ > 0, η ∈ (0,1), μ'' > 0 and c_δ ∈ (0,1).

In particular the posterior contracts at **M_n (n/log n)^{−α/(2α+1)}**. **No classical input is assumed:** B-spline stability for q = 1 and the one-block approximation for this class are proved inside the development. This is Assumption 2 derived for a concrete function space.

**On coverage.** The prior does not depend on α. The dictionary depends only on b, and it covers every α with β_k(α) ≤ b_k **for which the relevant approximation input holds**:
- Fourier: every α_k > 0, periodic f₀, given Jackson.
- Splines: the regimes of §2, namely 0 < α ≤ q (d = 1 or isotropic), integer α_k ≤ q (anisotropic), and, with no assumption, q = 1, d = 1, 0 < α ≤ 1.

For example, with q = 1 and α = 2, the one-block property does not hold uniformly over a nontrivial C²([0,1]) ball: f₀(x) = x is a counterexample, since order-1 splines on cells of width h have uniform error at least h/2. Individual truths, such as constants, can still satisfy it. So that pair is not covered as a class (Astra's spec review and Gate B).

**Not claimed:**
- End-to-end results with a general prior. They are stated for the horseshoe; the abstract corollary covers general priors satisfying Assumption 3.
- Specific values of C_sp, C_ε.
- Rates for non-integer anisotropic α with B-splines (G5).
- Splines with q ≥ 2 without the classical inputs.

## 6. Non-vacuity (`CorNonVacuity.lean`, `CorNonVacuityS.lean`, optional `Jackson.lean`)

Instance: d = 1, α = 1, b = 1 (so β = r = D = 1/3), design x_i = i/n, σ = 1, η = 1/2, μ'' = 1.

- **`corHorseshoe_nonvacuity`.** Fourier dictionary (M_n = n), f₀ = ψ₁ = √2 cos 2πx, C_sp = 1, C_app = 0, E = 2, C_ε = 1, c_δ = 1/2, K = √2. Every hypothesis of the horseshoe corollary holds, and `corHyp_nonvacuity` then gives `CorHyp` for the horseshoe prior. Here f₀ is a single atom, so this instance tests that the hypotheses are consistent, not the approximation.
- **`corFourier_nonvacuity`.** ψ₁ lies in the periodic Hölder–Zygmund ball of order 1, difference order 2, radius 30.
- **`bsplineReadout_one`, `splineOneBlock_one`, `corBSpline_nonvacuity`, `corBSpline_instance_conclusion`.** The B-spline end-to-end corollary for f₀ = 1, q = 1, with no assumed input.
- **`holderBall1_id`, `corHolder_id_conclusion`.** f₀(x) = x lies in the Lipschitz ball of radius 1. `cor_holder` then gives Corollary 1 for f₀(x) = x, which is outside every finite order-1 spline span and so has a **positive uniform approximation error on [0,1]**. Design i/n, b = 1, rate M_n (n/log n)^{−1/3}, no assumed input. Caveat (Gate B): with b = 1 the finest grid has 2^{⌈log₂ n⌉} ≥ n cells, so the dictionary can interpolate the n design values exactly. The best *empirical* approximation error of this instance is therefore zero. The whole-class theorem `cor_holder` is unaffected.
- **`jackson_lip`, `corFourierHalf_nonvacuity`, `corFourier_instance_conclusion` (`Jackson.lean`).** The Jackson inequality for 0 < α < 1, r = 1, and the Fourier end-to-end corollary for ψ₁ at smoothness 1/2 with no assumed input (rate (n/log n)^{−1/4}).

**Not shown:**
- That `JacksonIneq` holds for α ≥ 1 or for any r ≥ 2 (it is proved only for 0 < α < 1, r = 1).
- That `SplineOneBlock` / `SplineOneBlockCube` are satisfiable for q ≥ 2 or d ≥ 2 beyond constants.
- That `BSplineReadout` holds for q ≥ 2.

These rest on the literature (§2).

## 7. Sanity lemmas (`CorSanity.lean`)

- Isotropic reductions: α* = α and β_k = 1/(2α + d).
- Univariate α = 1: r = D = β = 1/3.
- Anisotropic (1, 2): α* = 4/3, r = 2/7, β = (2/7, 1/7).
- Finite differences of order 1 and 2; constants have zero differences; constants lie in HZ balls.
- Values of the frequency map, the budgets and the multipliers; Q_1 returns the mean.
- Spline dimensions, union sizes and level choices; dictionary sizes for small n.
- Lean conventions: N = n/log 1 = 0, and τ = 1/16 for J = 2, n = 4.
