# What the Lean statements say

This is a plain-mathematics reading of the formal statements, written so you can check them against the paper without reading Lean. The statements themselves live in [`LargePrior/Spec.lean`](../LargePrior/Spec.lean) (Theorem 1, the Horseshoe and the dictionaries), [`LargePrior/CorSpec.lean`](../LargePrior/CorSpec.lean) (Corollary 1 and the approximation lemmas) , [`LargePrior/HorseshoePaper.lean`](../LargePrior/HorseshoePaper.lean) (the Horseshoe paragraph of Section 2) and [`LargePrior/ChebSpec.lean`](../LargePrior/ChebSpec.lean) (the Chebyshev dictionary, §§10–12). [`AxiomCheck.lean`](../AxiomCheck.lean) pins each theorem to its statement.

## 1. Setting

Functions are identified with their values at the n design points. The dictionary is the n × J matrix X with entries X_{ij} = ξ_j(x_i), and f_θ = Xθ. The design may change with n (it is a triangular array).

| Lean | Meaning |
|---|---|
| `empNorm u` | ‖u‖_{2,n} = (n⁻¹ Σᵢ uᵢ²)^{1/2} |
| `numLarge δ θ` | #{j : \|θ_j\| > δ} |
| `prior J π` | the product of J copies of the law with density π (iid coordinates) |
| `dataLaw σ v` | the law of Y = v + ε, with εᵢ iid N(0, σ²); P₀ is `dataLaw σ f₀` |
| `posterior σ X f₀ Π y` | Bayes' formula, Π(H \| y) = ∫_H p_θ(y) dΠ / ∫ p_θ(y) dΠ, written with the likelihood ratio against f₀ |
| `sRate`, `epsRate` | s_n = max{a_n, ⌈n ε̄_n² / log J_n⌉} and ε_n = (s_n log J_n / n)^{1/2} |

E₀ is a genuine expectation under P₀. The posterior is a probability measure for every y. The lemma `posterior_ref_invariant` shows that it does not depend on the reference point used in the likelihood ratio, so it is the usual Bayes posterior.

**Assumptions at a fixed n:**

- `BasisBound X K` (Assumption 1): every column has ‖·‖_{2,n} ≤ K.
- `SparseApprox X f₀ ε̄ δ E a θ₀ S` (Assumption 2, with ξ*_n = S): ‖f₀ − Xθ₀‖_{2,n} ≤ ε̄, at most a coordinates of θ₀ exceed δ, every coordinate is at most E in absolute value, |S| = a, and |θ₀ⱼ| ≤ δ for j ∉ S.
- `WG3`: Π₁{|t| > δ} ≤ J^{−(1+μ)}.
- `WG4`: Π{Σ_{j∉S} |θ_j| ≤ η ε̄} ≥ exp(−c₄ n ε̄²). This is the paper's −log Π(…) ≤ c₄ n ε̄² with the logarithm removed.
- `WG5`: there is π_low > 0 with π(t) ≥ π_low for almost every |t| ≤ E, and a [log a + 2 log(1/ε̄) − log π_low] ≤ c₅ n ε̄². The paper's version, with the pointwise infimum, implies this (`wg5Paper_implies_wg5`).

## 2. Theorem 1

**`AsymptoticStatement`** (proved by `asymptotic_theorem`).

*Hypotheses:*

- constants σ > 0, K > 0, 0 < η < 1, μ > 0, c₄ ≥ 0 and c₅ ≥ 0;
- J_n → ∞;
- the standing requirements n ε̄_n² → ∞, δ_n ≤ ε̄_n/J_n and s_n log J_n / n → 0;
- any sequence M_n → ∞;
- for all large n:
  - π_n is a probability density;
  - ε̄_n, δ_n and E_n are positive;
  - 1 ≤ a_n ≤ J_n;
  - Assumption 1 holds with the fixed K;
  - Assumption 2 holds for some (θ₀, ξ*_n), and (WG4) holds for that ξ*_n;
  - (WG3) and (WG5) hold.

*Conclusions:* let A = ⌈(C₁ + 1)/μ⌉. Here C₁ = c₄ + c₅ + 1 + √2 L̃/σ + L̃²/(2σ²) and L̃ = 1 + K(1 + 2η), so A depends only on (K, σ, μ, η, c₄, c₅). Then, for all large n,

- E₀ Π(‖f_θ − f₀‖_{2,n} > M_n ε_n | Y) ≤ **5** e^{−n ε̄_n²};
- E₀ Π(#{j : |θ_j| > δ_n} > A s_n | Y) ≤ 2 e^{−n ε̄_n²};
- for every ζ > 0, P₀{Π(· | Y) > ζ} → 0 for both events, which is convergence in P₀-probability.

**`MasterStatement`** (`master_theorem`) is the same result at a single n. It replaces the eventual conditions by seven explicit inequalities: ε̄ ≤ η, J^μ ≥ 2, n ε̄² ≥ log 2, log J ≥ 1 + log 97, M ≥ 16K, M² ≥ 16σ²(2A + 1), and M² ≥ 64σ²(C₁ + 1).

## 3. The Horseshoe

- `horseshoePDF τ t` = ∫₀^∞ φ(t; 0, λ²τ²) · 2/(π(1 + λ²)) dλ. At t = 0 the true value is +∞, and Lean stores 0 there. This is a single point, so the law is unchanged. It is also why (WG5) is stated almost everywhere.
- **`HorseshoeDensityStatement`** (`horseshoe_isProbDensity`): for τ > 0 this is a probability density.
- **`HorseshoePaperConditionsStatement`** (`horseshoe_paper_conditions`) is the paragraph after Theorem 1. *Hypotheses:*
  - J_n → ∞ and n ε̄_n² / log J_n → ∞;
  - for all large n:
    - τ_n ≤ J_n^{−(2+μ′)}/√n;
    - −log τ_n ≤ C log J_n and log E_n ≤ C log J_n;
    - δ_n ≥ c_δ ε̄_n/J_n;
    - a_n log J_n ≤ C n ε̄_n².

  *Conclusion:* there is a c₅ ≥ 0 such that, for every μ ∈ (0, μ′) and all large n,
  - (WG3) holds with μ;
  - (WG4) holds with c₄ = 1 for every index set of size a_n;
  - (WG5) holds with c₅.

  Only the lower half of δ_n ≍ ε̄_n/J_n is needed.
- **`HorseshoeAssumption3Statement`** and **`HorseshoeAssumption3MuStatement`** are the same result with explicit constants. Here the scale condition is written τ_n ≤ c_τ J_n^{−(2+μ″)}/√n, with μ″ playing the role of the paper's μ′. The constants are μ = μ″/2 (or any μ < μ″), c₄ = 1 and c₅ = B(6 + 5B). **`MainHorseshoeStatement`** combines this with Theorem 1.

## 4. The dictionaries (Assumption 1)

- `fourierAtom`: ψ₀ = 1, ψ_{2j−1} = √2 cos(2πjx), ψ_{2j} = √2 sin(2πjx), with tensor products over coordinates.
  - **`FourierBasisStatement`**: any finite family of tensor Fourier atoms on [0,1]^d, at any design, satisfies Assumption 1 with K = 2^{d/2}.
- `bspline q K i`: the order-q B-spline on K equal subintervals with clamped knots, built by the Cox–de Boor recursion. Tensor products are taken over coordinates.
  - **`BSplineBasisStatement`**: any finite family of tensor B-spline atoms, of any orders and resolutions, with the design in [0,1]^d, satisfies Assumption 1 with K = 1. This includes multiresolution unions.
- `chebAtom`: φ₀ = 1, φ_j(x) = √2 T_j(2x − 1) for j ≥ 1, with T_j the Chebyshev polynomial of the first kind, and tensor products over coordinates.
  - **`ChebyshevBasisStatement`**: any finite family of tensor Chebyshev atoms, with the design in [0,1]^d, satisfies Assumption 1 with K = 2^{d/2}, since |φ_j| ≤ √2 on [0,1].

## 5. Corollary 1

**`CorollaryStatement`** (`corollary_main`).

*Hypotheses (`CorHyp`):*

- d ≥ 1 and α_k > 0, with b_k ≥ β_k.
- L_{n,k} ≍ n^{b_k} and J_n ≍ ∏_k L_{n,k}, two-sided and for large n.
- σ > 0.
- Assumption 1 with a fixed K.
- The sparse approximation profile (`ProfileAt`) holds for all large n with constants C_sp > 0, C_app ≥ 0 and E > 0. Concretely, for every rectangle 1 ≤ m_k ≤ L_{n,k}, some θ has #supp θ ≤ C_sp ∏ m_k, ‖f₀ − f_θ‖_{2,n} ≤ C_app Σ_k m_k^{−α_k}, and ‖θ‖_∞ ≤ E.
- C_ε ≥ d·C_app and c_δ ∈ (0, 1).
- The sequences are those of the paper:
  - N_n = n/log J_n;
  - m_{n,k} = ⌈N_n^{β_k}⌉;
  - a_n = ⌈C_sp ∏ m_{n,k}⌉;
  - ε̄_n = C_ε N_n^{−r};
  - E_n = E;
  - δ_n = c_δ ε̄_n/J_n.
- Assumption 3 holds for these sequences. (WG4) is needed for one index set of size a_n; `wg4_of_card_eq` moves it to any other set of that size, because the prior is iid.

*Conclusions:* let A be the integer of Theorem 1.

0. **Theorem 1 applies.** For every M_n → ∞, the hypotheses of Theorem 1 hold at these sequences (`cor_asymptoticHyp`). These include Assumption 2 and the standing requirements.
1. **Orders.** For some C > 0 and all large n:
   - a_n ≤ s_n ≤ C a_n;
   - a_n lies between C⁻¹(n/log n)^D and C(n/log n)^D;
   - ε_n lies between C⁻¹(n/log n)^{−r} and C(n/log n)^{−r}.
2. **Bounds.** Set A′ = A C_s/C_sp and c = C_ε²/C_s, where C_a = 2^d C_sp + 1 and C_s = max{C_a, C_ε² + 1} (proof of Corollary 1 in the Appendix). For every M_n → ∞ and all large n:
   - E₀ Π(‖f_θ − f₀‖_{2,n} > M_n ε_n | Y) ≤ 5 e^{−c n ε_n²};
   - E₀ Π(#{j : |θ_j| > δ_n} > A′ a_n | Y) ≤ 2 e^{−c n ε_n²}.
3. Both posterior probabilities tend to 0 in P₀-probability.

Here ε_n and s_n are Theorem 1's `epsRate` and `sRate` at the corollary's sequences, so part (ii) has exactly the paper's radius, exponent and constants, with 5 in place of 6.

**`CorHorseshoeStatement`** (`cor_horseshoe`) gives the same conclusions for the Horseshoe with τ_n = J_n^{−(2+μ″)}/√n. Assumption 3 is derived rather than assumed. The scale τ_n depends only on n and J_n, not on α.

## 6. The sparse approximation lemmas (B-spline and Fourier; Chebyshev in §11)

The lemmas are stated in sup-norm. The empirical-norm profile then follows at any design.

- **`FourierProfileStatement`** (Fourier profile lemma). Take f₀ in the periodic anisotropic Hölder–Zygmund ball `HZBall α r R`, with integers r_k > α_k, and assume the Jackson inequality in each coordinate. Then for every dictionary size and every rectangle m, some θ satisfies:
  - #supp θ ≤ ∏ m_k;
  - sup |f₀ − f_θ| ≤ C R Σ_k m_k^{−α_k};
  - |θ_ν| ≤ R.
- **`BSplineProfileStatement`** and **`BSplineProfileCubeStatement`** (B-spline profile lemma, anisotropic and isotropic parts). Assume B-spline stability (`BSplineReadout`) and the one-block spline approximation of f₀ (`SplineOneBlock`, `SplineOneBlockCube`). Then the multiresolution tensor dictionary has the profile, with constants uniform in the truncation level, the rectangle and the design.

The classical inputs enter as named hypotheses. They are not axioms.

| Input | Classical source | Proved in Lean for |
|---|---|---|
| `JacksonIneq` | Jackson–Stechkin inequality | 0 < α < 1, r = 1 (`jackson_lip`) |
| `BSplineReadout` | B-spline stability (de Boor; Schumaker Thm 4.41) | order q = 1 (`bsplineReadout_one`) |
| `SplineOneBlock`, `SplineOneBlockCube` | spline approximation of Hölder functions (Schumaker Thms 6.10, 12.7; Shen and Ghosal 2015) | q = 1, d = 1, f₀ in a C^α([0,1]) ball with 0 < α ≤ 1 (`splineOneBlock_holder`) |

## 7. End-to-end versions of Corollary 1

These derive Assumption 2 from a function class rather than assuming a profile. All of them use the Horseshoe. In each one, the constants C_sp and C_ε are chosen first, depending only on the class. They then work for every truth in the class, every admissible exponent b, every design, every σ, every η ∈ (0,1), every μ″ > 0 and every c_δ ∈ (0,1).

- **`CorFourierStatement`**: periodic f₀ in `HZBall`, given Jackson, with the Fourier dictionary truncated at frequency M_{n,k} = ⌈n^{b_k}⌉ in coordinate k, so 2M_{n,k} + 1 atoms per coordinate and J_n = ∏_k (2M_{n,k} + 1).
- **`CorChebyshevStatement`**, **`CorChebyshevExStatement`** and **`CorChebyshevHolderStatement`**: the tensor Chebyshev dictionary on [0,1]^d for f₀ in the sectional Hölder class; see §§10–12.
- **`CorBSplineStatement`** and **`CorBSplineCubeStatement`**: multiresolution B-splines with H_{n,k} = ⌈b_k log₂ n⌉ levels, given the spline inputs above.
- **`CorHolderStatement`** (`cor_holder`) needs **no assumed input**. Take any f₀ in the C^α([0,1]) ball with 0 < α ≤ 1, any b ≥ 1/(2α + 1), any design in [0,1], order-1 multiresolution B-splines and the Horseshoe. The posterior then contracts at M_n ε_n, with ε_n ≍ (n/log n)^{−α/(2α+1)}.

## 8. Checks that the hypotheses are not vacuous

Concrete instances satisfy every hypothesis, and the theorems are applied to them:

- `nonvacuity` (Theorem 1 with the Horseshoe);
- `corHyp_nonvacuity` and `corHorseshoe_nonvacuity` (Corollary 1);
- `corBSpline_instance_conclusion` (f₀ = 1);
- `corHolder_id_conclusion` (f₀(x) = x, outside every finite order-1 spline span);
- `corFourier_instance_conclusion` (a Fourier instance at smoothness ½, with Jackson proved);
- `cor_chebyshev_witness_two` (Chebyshev, d = 2, anisotropic α = (½, ¾), f₀(x) = x₁x₂, design (i/n, 1 − i/n)) and `cor_chebyshev_witness_one` (Chebyshev, d = 1, α = ½, f₀(x) = x), both with C_app > 0 and nothing assumed;
- `cheb_witness_sq`, `cheb_witness_sq_transfer`, `chebCtr_two_three` and `cheb_witness_sq_mul` (the Chebyshev class beyond α ≤ 1: x ↦ x² lies in the C²([0,1]) ball of radius 2, the transfer applies to it at r = 3, and C_tr(2) = 1 + 6π²; x₁²x₂ lies in the sectional class of radius 2 at α = (2, ½)).

[`ChebChecks.lean`](../LargePrior/ChebChecks.lean) also proves the three Chebyshev sanity statements of §11.

[`Sanity.lean`](../LargePrior/Sanity.lean) and [`CorSanity.lean`](../LargePrior/CorSanity.lean) evaluate small cases that would expose a mistyped definition: low-order B-splines, the first Fourier atoms, the exponent algebra, and dictionary sizes.

## 9. Modelling choices

- **(WG4) as a lower bound on a probability.** It is stated as Π(…) ≥ e^{−c₄ n ε̄²}, which is equivalent to the paper's −log Π(…) ≤ c₄ n ε̄². This avoids Lean's convention log 0 = 0.
- **(WG5) almost everywhere.** A pointwise infimum depends on the version of the density. The a.e. bound does not, and it is implied by the paper's form. This matters for the Horseshoe, whose density is infinite at 0.
- **Eventual hypotheses.** Every condition on the sequences is required only for large n. J_n ≥ 2 is not assumed; it follows from J_n → ∞.
- **Explicit constants.** Theorem 1's A and Corollary 1's A′ and c are given by formulas, not by existence claims.
- **Horseshoe density at 0.** It is defined as a Bochner integral, which Lean sets to 0 where the integrand is not integrable. That happens only at t = 0, a null set, so the law is unchanged.
- **Classical approximation theorems as hypotheses.** For splines with α > 1, for d ≥ 2, and for the anisotropic spline class, the Hölder classes are not defined in Lean. The statements read "for every f₀ with the one-block approximation property", which the cited theorems provide for f₀ in the class. The periodic Hölder–Zygmund class used for Fourier *is* defined, because the proof uses its structure.

## 10. The Chebyshev dictionary: definitions

The statements are in [`LargePrior/ChebSpec.lean`](../LargePrior/ChebSpec.lean), which holds definitions and `Prop`s only.

- `chebFold u` = x(u) = (1 + cos 2πu)/2: a smooth, even, 1-periodic map of ℝ onto [0,1] (the fold).
- `chebAtom j`: φ₀ = 1 and φ_j(x) = √2 T_j(2x − 1) for j ≥ 1. `chebTensor`, `ChebIdx L` (indices 0 ≤ j_k ≤ L_k − 1) and `chebSeries` give the tensor atoms and the series f_θ = Σ_j θ_j Φ_j.
- `HolderBallIcc α R f`: the ball of radius R in C^α([0,1]). Put s = ⌈α⌉ − 1 and β = α − s ∈ (0,1], so β = 1 at integer α. Then f is s times continuously differentiable on [0,1], with one-sided derivatives at the endpoints; |f^{(j)}| ≤ R for j ≤ s; and f^{(s)} is β-Hölder with constant R.
- `SecHolderBall α R f₀`: the sectional class C^α_sec([0,1]^d; R). f₀ is continuous on the cube, and every one-dimensional section through a point of the cube (faces included) in direction k lies in `HolderBallIcc (α k) R`.
- `chebKappa s β` = Σ_{k=1}^{s} (1 + 2k^β) 2^{−k} S(s,k), where S(s,k) are Stirling numbers of the second kind; its value at s = 0 is 1. `chebCtr α r` = C_tr(α) = 1 + 2^{r−s−1} π^β (2π)^s κ_{s,β}.
- `chebC`, `chebCk`, `chebCapp`: the profile constants C = max{2, 4·3^α C_J C_tr(α)}, c_k = R·max{2, 4·3^{α_k} C_k C_tr(α_k)} and C_app = 3^{d−1} max_k c_k.
- `chebDesign e x` and `chebXe`: the design matrix of the dictionary for any enumeration e : Fin J ≃ `ChebIdx L` of its atoms. `chebL`, `chebJ`, `chebX`: the ceiling sizes L_{n,k} = ⌈n^{b_k}⌉, J_n = ∏_k L_{n,k}, and the corresponding sequence of design matrices.

## 11. The Chebyshev statements

| Statement | Proved by (module) |
|---|---|
| `ChebTransferStatement` (smoothness transfer under the fold) | `cheb_transfer_statement` (`ChebTransferHigh`) |
| `ChebyshevBasisStatement` (Assumption 1) | `chebyshev_basis` (`ChebBasis`) |
| `ChebyshevProfileStatement` (Lemma chebyshev-profile) | `chebyshev_profile` (`ChebMain`) |
| `ChebyshevAnisoProfileStatement` (Lemma chebyshev-aniso-profile) | `chebyshev_aniso_profile` (`ChebMain`) |
| `ChebyshevProfileAtStatement` (the profile at a design) | `chebyshev_profile_at` (`ChebMain`) |
| `CorChebyshevStatement` (Corollary 1, explicit constants) | `cor_chebyshev` (`ChebMain`) |
| `CorChebyshevExStatement` (Corollary 1, existential constants) | `cor_chebyshev_ex` (`ChebMain`) |
| `CorChebyshevHolderStatement` (Corollary 1, α ∈ (0,1)^d, nothing assumed) | `cor_chebyshev_holder` (`ChebEndToEnd`) |
| `ChebSanityHolder`, `ChebSanityCtr`, `ChebSanityAnisoUniv` | `cheb_sanity_holder`, `cheb_sanity_ctr`, `cheb_sanity_aniso_univ` (`ChebChecks`) |

- **`ChebTransferStatement`.** For every α > 0, every integer r > α and every f in the ball of radius R of C^α([0,1]), the folded function f∘x lies in the periodic Hölder–Zygmund ball `HZBall1 α r` of radius C_tr(α) R. Smoothness on [0,1] becomes periodic smoothness of the same order. The internal proofs in `ChebProfile` and `ChebEndToEnd` use it through the fixed-(α, r) form `ChebTransferPremise α r`, and `ChebMain` discharges that premise with `cheb_transfer_statement`. No headline statement takes `ChebTransferPremise` as a hypothesis.
- **`ChebyshevProfileStatement`.** Take α > 0, R ≥ 0, f in the ball of radius R of C^α([0,1]) and m ≥ 1. There is a coefficient map ϑ with ϑ_j = 0 for j ≥ m and |ϑ_j| ≤ R such that, for every difference order r > α, every Jackson constant C_J with `JacksonIneq α r C_J`, and every dictionary size L ≥ m,
  sup_{[0,1]} |f − Σ_{j<L} ϑ_j φ_j| ≤ max{2, 4·3^α C_J C_tr(α)} · R · m^{−α}.
  ϑ is chosen before L, r and C_J, so the coefficients depend on none of them. The empirical-norm form follows because the empirical norm is at most the sup norm; Corollary 1 uses it through `ChebyshevProfileAtStatement`.
- **`ChebyshevAnisoProfileStatement`.** The same for d ≥ 1, f₀ in `SecHolderBall α R` and a rectangle m with every m_k ≥ 1. The coefficient map ϑ on ℕ^d is supported in ∏_k {0,…,m_k − 1}, has |ϑ_j| ≤ R, and is chosen before the orders r_k > α_k, the Jackson constants C_k and the sizes L ≥ m. The error is sup_{[0,1]^d} |f₀ − Σ_{j ∈ ChebIdx L} ϑ_j Φ_j| ≤ 3^{d−1} max_k c_k · Σ_k m_k^{−α_k}. At d = 1 it implies the univariate statement (`ChebSanityAnisoUniv`).
- **`ChebyshevProfileAtStatement`.** For d ≥ 1, 0 < α_k < r_k, Jackson in each coordinate, R ≥ 0, f₀ in the sectional class, any sizes L, any enumeration e of the atoms and any design in [0,1]^d, the profile `ProfileAt` of Corollary 1 holds for the design matrix with C_sp = 1, C_app = 3^{d−1} max_k c_k and E = R.
- **`CorChebyshevStatement`.** Take d ≥ 1 and assume `JacksonIneq (α k) (r k) (C_k)` for every k. Then `CorChebExplicit` holds:
  - **For:** α_k > 0 with integers r_k > α_k (hypotheses of `CorChebHyp`); every R > 0 and C_ε ≥ d·C_app; every b_k ≥ β_k; every L_{n,k} ≍ n^{b_k} with J_n ≍ ∏_k L_{n,k} (`SizesComparable`); every enumeration of the atoms; every f₀ in C^α_sec([0,1]^d; R); every design in [0,1]^d; every σ > 0, η ∈ (0,1), μ″ > 0 and c_δ ∈ (0,1).
  - **The conclusion `CorChebOutcome` holds,** with C_sp = 1 and E = R. It is the conclusion of `CorFourierStatement`:
    - Assumption 3 with μ = μ″/2, c₄ = 1 and some c₅ ≥ 0;
    - Theorem 1's hypotheses for every M_n → ∞;
    - parts (i)–(iii) of Corollary 1 with K = 2^{d/2}.
- **`CorChebyshevExStatement`.** The form with the shape of `CorFourierStatement`: ceiling sizes ⌈n^{b_k}⌉, and constants C_sp, C_ε, E > 0 that exist and depend only on (d, α, r, C_J, R). `CorChebyshevStatement` implies it.
- **`CorChebyshevHolderStatement`.** For α ∈ (0,1)^d there are Jackson constants C_k, depending on α only, with `JacksonIneq (α k) 1 (C_k)`, and `CorChebExplicit` holds at r = 1 with them. Nothing is assumed: Jackson comes from `jackson_lip` and the transfer from `cheb_transfer_le_one`.
- **Sanity statements.** A failure would mean a definition is wrong.
  - `ChebSanityHolder`: for 0 < α ≤ 1, `HolderBallIcc α R f ↔ HolderBall1 α R f`.
  - `ChebSanityCtr`: with r = ⌊α⌋ + 1, C_tr(½) = 1 + √π, C_tr(1) = 1 + 2π, C_tr(2) = 1 + 6π² and C_tr(3) = 1 + 22π³.
  - `ChebSanityAnisoUniv`: the anisotropic profile implies the univariate one.

## 12. Notes on the Chebyshev statements

- **Sizes and enumeration.** `CorChebyshevStatement` and `CorChebyshevHolderStatement` cover any sizes with L_{n,k} ≍ n^{b_k} and any enumeration of the atoms; the enumeration forces J_n = ∏_k L_{n,k}. `CorChebyshevExStatement` fixes the ceiling sizes ⌈n^{b_k}⌉, as `CorFourierStatement` fixes M_{n,k} = ⌈n^{b_k}⌉.
- **Horseshoe only.** Like `CorFourierStatement` and `cor_horseshoe`, the Chebyshev corollaries specialise the prior of Assumption 3 to the Horseshoe with τ_n = J_n^{−(2+μ″)}/√n (`corTau`), μ = μ″/2 and c₄ = 1. For another prior, combine `CorollaryStatement` (`corollary_main`) with `ChebyshevBasisStatement` and `ChebyshevProfileAtStatement`. These supply Assumption 1 and the profile, and the prior supplies Assumption 3.
- **Displayed constants.** The paper gives the Chebyshev profile with explicit constants. The profile statements, `CorChebyshevStatement` and `CorChebyshevHolderStatement` keep them, with C_sp = 1, E = R and, in the corollaries, any C_ε ≥ d·C_app; only the convenience form `CorChebyshevExStatement` is existential. The shipped Fourier and B-spline statements assert only that constants exist: `FourierProfileStatement` has ∃ C ≥ 0, and `CorFourierStatement`, `CorBSplineStatement`, `CorBSplineCubeStatement` and `CorHolderStatement` have ∃ C_sp, C_ε, E > 0.
- **The difference order.** The order r_k of the Hölder–Zygmund norm is an explicit argument with r_k > α_k wherever it is used. The coefficient map does not depend on it.
- **Scope of the no-input corollary.** `CorChebyshevHolderStatement` assumes nothing, but only for α ∈ (0,1)^d, because Jackson is proved in Lean only for 0 < α < 1 at r = 1. For α_k ≥ 1, `JacksonIneq` has no Lean witness here; the profiles and `CorChebyshevStatement` then hold given it as a hypothesis. The transfer itself is proved for every α > 0 and r > α.
- **Not formalized.** The Gauss–Chebyshev Gram identity, the arcsine-weight coefficient formulas, the inclusions between the classes, and the Jackson inequality for α ≥ 1. No statement depends on the first three; for α_k ≥ 1 the Jackson inequality enters as an explicit hypothesis, not a proved theorem.
- **Inherited from the shipped definitions.** These hold for the Fourier and B-spline corollaries too:
  - (WG5) is checked almost everywhere;
  - the prefactor in part (ii) is 5, which implies the paper's 6;
  - c₅ is chosen after f₀, the design, σ, η and c_δ (Corollary 1 is pointwise in f₀).
