# STATEMENTS: what the Lean definitions and theorems say, in plain mathematics

Lean file: `lean/LargePrior/Spec.lean`. Decisions marked (D*k*) and gaps (G*k*) are in ASSUMPTIONS.md. Read this file to check that the Lean statements say what the paper says; no Lean knowledge is needed.

## 1. Objects

| Lean | Meaning |
|---|---|
| `empNorm u` | ‖u‖_{2,n} = (n⁻¹ Σᵢ uᵢ²)^{1/2} for u ∈ ℝⁿ. |
| `numLarge δ θ` | N_δ(θ) = #{j : \|θ_j\| > δ}. |
| `IsProbDensity π` | π : ℝ → ℝ is measurable, π ≥ 0, ∫ π = 1. |
| `coordPrior π` | The probability law with density π on ℝ (one coordinate of the prior). |
| `prior J π` | Π = product of J copies of `coordPrior π` on ℝ^J (iid coordinates). |
| `dataLaw σ v` | P_v = law of Y = v + ε, εᵢ iid N(0, σ²), on ℝⁿ. P₀ = P_{f₀}. |
| `likRatio σ f₀ g y` | L(g; y) = exp{σ⁻² Σᵢ (yᵢ − f₀ᵢ)(gᵢ − f₀ᵢ) − (2σ²)⁻¹ Σᵢ (gᵢ − f₀ᵢ)²} = p_g(y)/p_{f₀}(y). (D6) |
| `evidence σ X f₀ Π y` | D(y) = ∫ L(Xθ; y) dΠ(θ). |
| `posterior σ X f₀ Π y` | The posterior law Π(· \| y): Π(H \| y) = ∫_H L(Xθ; y) dΠ(θ) / D(y). (D6) |
| `farSet X f₀ r` | U(r) = {θ : ‖Xθ − f₀‖_{2,n} > r}. |
| `denseSet δ m` | Θᶜ(m) = {θ : N_δ(θ) > m}. |
| `sRate n J a ε̃` | s = max{a, ⌈n ε̃² / log J⌉}. |
| `epsRate n J a ε̃` | ε = (s log J / n)^{1/2}. |
| `Ltil, C0, CPi, C1, Aconst` | L̃ = 1 + K(1 + 2η); C₀ = √2 L̃/σ + L̃²/(2σ²); C_Π = c₄ + c₅ + 1; C₁ = C_Π + C₀; A = ⌈(C₁ + 1)/μ⌉. |

Functions are identified with their values at the design points, the dictionary with the n × J matrix X_{ij} = ξ_j(x_i), and f_θ = Xθ (D5).

## 2. Assumptions at a fixed n

- `BasisBound X K` (Assumption 1): every column of X has ‖·‖_{2,n} ≤ K.
- `SparseApprox X f₀ ε̃ δ E a θ₀ S` (Assumption 2 with ξ*_n = S): ‖f₀ − Xθ₀‖_{2,n} ≤ ε̃; N_δ(θ₀) ≤ a; max_j \|θ₀ⱼ\| ≤ E; S has exactly a elements; \|θ₀ⱼ\| ≤ δ for j ∉ S. (N_δ(θ₀) ≤ a is implied by the last two conditions; it is kept to match the paper's wording.)
- `WG3 π δ μ J`: Π₁{\|t\| > δ} ≤ J^{−(1+μ)}.
- `WG4 π J S η ε̃ c₄ n`: Π{θ : Σ_{j∉S} \|θ_j\| ≤ η ε̃} ≥ exp(−c₄ n ε̃²). Same as −log Π(...) ≤ c₄ n ε̃². (D1)
- `WG5 π E ε̃ c₅ a n`: there is π_low > 0 with π(t) ≥ π_low for (Lebesgue-)almost every \|t\| ≤ E, and a·[log a + 2 log(1/ε̃) − log π_low]₊ ≤ c₅ n ε̃². The paper's (WG5) with π_low = inf_{\|t\|≤E} π(t) implies this (`wg5Paper_implies_wg5`, `WG5Bridge.lean`); the converse is not claimed. For c₅ ≥ 0 the positive part [·]₊ is immaterial (`wg5_iff_noPos`). The Lean (WG5) is implied by, not equivalent to, the paper's for the horseshoe: Lean's `horseshoePDF` is 0 at t = 0 while the paper's density is +∞ there. (D2)

## 3. Theorem 1

**`MasterStatement` (Theorem 1 at a fixed n).** Suppose n ≥ 1, J ≥ 2, σ > 0, π is a probability density, ε̃, δ, E, K, η, μ > 0, c₄, c₅ ≥ 0, 1 ≤ a ≤ J, δ ≤ ε̃/J, Assumption 1, Assumption 2 for some (θ₀, S) with (WG4) for that S, (WG3), (WG5), and

(e1) ε̃ ≤ η, (e2) J^μ ≥ 2, (e3) n ε̃² ≥ log 2, (e4) log J ≥ 1 + log 97, (e5) M ≥ 16K, (e6) M² ≥ 16σ²(2A + 1), (e7) M² ≥ 64σ²(C₁ + 1).

Then E₀ Π(‖f_θ − f₀‖_{2,n} > M ε \| Y) ≤ 5 e^{−n ε̃²} and E₀ Π(N_δ(θ) > A s \| Y) ≤ 2 e^{−n ε̃²}. (D7)

**`AsymptoticStatement` (Theorem 1 as in the paper) = `AsymptoticHyp` ⇒ `AsymptoticConclusion`.** Hypotheses (`AsymptoticHyp`): constants σ > 0, K > 0, 0 < η < 1, μ > 0, c₄, c₅ ≥ 0; J_n → ∞; n ε̃_n² → ∞; s_n log J_n / n → 0; M_n → ∞; and, for all sufficiently large n: π_n is a probability density; ε̃_n, δ_n, E_n > 0; 1 ≤ a_n ≤ J_n; δ_n ≤ ε̃_n/J_n; Assumption 1 with the fixed K; Assumption 2 with (WG4) for its S (D3); (WG3); (WG5). Conclusions (`AsymptoticConclusion`): for all large n the two bounds above hold (constants 5 and 2), and for every ζ > 0, P₀{Π(‖f_θ − f₀‖_{2,n} > M_n ε_n | Y) > ζ} → 0 and P₀{Π(N_{δ_n}(θ) > A s_n | Y) > ζ} → 0 (D14). Every condition on the sequences is needed only for large n (D13), which is what the manuscript says (the standalone document asks for every n), so the Lean theorem implies both.

Differences from the paper: constant 5 instead of the manuscript's 6 (the standalone version already has 5); A explicit; (WG4) in an equivalent form (D1); (WG5) in the almost-everywhere form of §2, which is implied by the paper's pointwise-infimum (WG5) (D2).

## 4. Horseshoe prior

- `halfCauchyPDF λ` = 2/(π(1 + λ²)) for λ > 0, else 0.
- `horseshoePDF τ t` = π_τ(t) = ∫₀^∞ φ(t; 0, λ²τ²) f_{C⁺}(λ) dλ, with φ the normal density. At t = 0 the true value is +∞ and Lean stores 0 (one point; no effect on the law). (D4)
- **`HorseshoeDensityStatement`:** for every τ > 0, π_τ is a probability density.
- **`HorseshoeAssumption3Statement` (Wei–Ghosal Theorem 3.3 in thesis notation).** Let J_n → ∞, n ε̃_n² → ∞, and constants η, μ'', c_δ, c_τ > 0, B ≥ 0. Suppose that for all large n: 1 ≤ a_n ≤ J_n; ε̃_n, E_n, τ_n > 0; δ_n ≥ c_δ ε̃_n/J_n; τ_n ≤ c_τ J_n^{−(2+μ'')}/√n; a_n log J_n ≤ B n ε̃_n²; log(1/ε̃_n) ≤ B log J_n; log(1/τ_n) ≤ B log J_n; log E_n ≤ B log J_n. Then for all large n, π_{τ_n} satisfies (WG3) with μ = μ''/2, (WG4) with c₄ = 1 for every S with \|S\| = a_n, and (WG5) with c₅ = B(6 + 5B). (D10, G1)
- **`MainHorseshoeStatement` = `MainHorseshoeHyp` ⇒ `AsymptoticConclusion`:** Theorem 1 with π_n = π_{τ_n}, where (WG3)–(WG5) and the density hypothesis are replaced by the hypotheses of the previous item, with μ = μ''/2, c₄ = 1, c₅ = B(6 + 5B). The hypotheses force c_δ ≤ 1 and B ≥ 2 + μ'' (G1). The choice μ = μ''/2 in the two frozen statements is one valid choice: any μ ∈ (0, μ'') works (§8).

## 5. Dictionaries

- `designMatrix ξ x`: X_{ij} = ξ_j(x_i).
- `fourierAtom ν x`: ψ₀ = 1, ψ_{2j−1}(x) = √2 cos(2πjx), ψ_{2j}(x) = √2 sin(2πjx). `fourierTensor ν x` = Π_k ψ_{ν_k}(x_k). (D12)
- **`FourierBasisStatement`:** every finite family of tensor Fourier atoms on [0,1]^d, at any design points, satisfies Assumption 1 with K = 2^{d/2}.
- `knot q K i` = clamp((i − q + 1)/K, 0, 1): q knots at 0, K − 1 interior knots j/K, q knots at 1.
- `bspl q K k i` = order-k B-spline (degree k − 1) by the Cox–de Boor recursion; `bspline q K i` = order-q B-spline B_i, i = 0, …, K + q − 2; `bsplineTensor` = product over coordinates. (D11)
- **`BSplineBasisStatement`:** every finite family of tensor B-spline atoms (any orders q ≥ 1, any K ≥ 1 subintervals, any indices; so any multiresolution union and any tensor product), with design points in [0,1]^d, satisfies Assumption 1 with K = 1.

## 6. Non-vacuity

`nonvacuity`: the concrete instance (Fourier dictionary ψ₀, …, ψ_{n+1} at x_i = i/n, f₀ = ψ₁, σ = 1, K = √2, a_n = 1, E_n = 1, ε̃_n = (n+1)^{−1/4}, δ_n = ε̃_n/J_n, τ_n = J_n^{−3}/√n, M_n = log(n+2), η = 1/2, μ'' = 1, c_δ = c_τ = 1, B = 4) satisfies `MainHorseshoeHyp`, i.e. every hypothesis of Theorem 1 for the horseshoe; so the hypotheses are not contradictory. `nonvacuity_conclusion` applies the theorem to it.

## 7. Sanity lemmas (Sanity.lean)

Special cases that would expose a wrongly written definition: B-splines of order 1 and 2 on small knot vectors, the first Fourier atoms, ‖c·1‖_{2,n} = |c|, and that the posterior does not depend on the reference point f₀ used in the likelihood ratio (so it is the Bayes posterior p_θ(y) dΠ(θ) / ∫ p_θ(y) dΠ(θ)).

## 8. Added 2026-11-03 (Corollary 1 update `cor_v2`, Theorem 1 update `v3`)

The statements above are unchanged. The following are new.

- **`wg4_of_card_eq` (`WG4Perm.lean`).** If (WG4) holds for one index set S, it holds for every set S' with |S'| = |S| (same π, J, η, ε̃, c₄, n). The prior is iid, so permuting coordinates maps S to S'. Corollary 1 assumes (WG4) for one set of size a_n and uses this to get it for the active set ξ*_n.
- **`wg5_iff_noPos`, `wg5Paper_implies_wg5` (`WG5Bridge.lean`).** For c₅ ≥ 0 the positive part [·]₊ in `WG5` is immaterial. The paper's (WG5), with the pointwise infimum π_inf = inf_{\|t\|≤E} π(t) > 0 and no positive part, implies the Lean almost-everywhere `WG5`. The converse is not claimed (see §2).
- **`HorseshoeAssumption3MuStatement` (`horseshoe_assumption3_mu`, `HorseshoePaper.lean`).** Wei–Ghosal Theorem 3.3 for the horseshoe (§4) with (WG3) for any μ ∈ (0, μ''), instead of the single choice μ''/2. The other hypotheses are those of `HorseshoeAssumption3Statement`; the conclusions are (WG3) with this μ, (WG4) with c₄ = 1 for every set of size a_n, and (WG5) with c₅ = B(6 + 5B).
- **`horseshoe_assumption3_of_mu`.** The frozen `HorseshoeAssumption3Statement` (μ = μ''/2) is the μ''/2 instance of `HorseshoeAssumption3MuStatement`.
- **`HorseshoePaperConditionsStatement` (`horseshoe_paper_conditions`, `HorseshoePaper.lean`).** The paper's conditions eq:hs-conditions imply Assumption 3 for the horseshoe. Suppose J_n → ∞, n ε̃_n²/log J_n → ∞, 1 ≤ a_n ≤ J_n, ε̃_n, E_n, τ_n > 0, and, for all large n: τ_n ≤ J_n^{−(2+μ')}/√n; −log τ_n ≤ C_τ log J_n; log E_n ≤ C_E log J_n; c_δ ε̃_n/J_n ≤ δ_n; a_n log J_n ≤ C_a n ε̃_n² (η > 0, μ' > 0, c_δ > 0). Then there is c₅ ≥ 0 such that for every μ ∈ (0, μ'), for all large n: (WG3) with μ, (WG4) with c₄ = 1 for every set of size a_n, and (WG5) with c₅. Only the lower half c_δ ε̃_n/J_n ≤ δ_n of δ_n ≍ ε̃_n/J_n is needed, and only η > 0. The paragraph's last sentence (the conditions hold for Corollary 1's sequences) is covered in Lean form by `cor_horseshoe_budget` and `CorHorseshoeHyp.corHyp`, which derive Assumption 3 for those sequences instead of restating eq:hs-conditions.
