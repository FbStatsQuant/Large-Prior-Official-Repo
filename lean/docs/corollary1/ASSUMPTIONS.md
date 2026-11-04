# ASSUMPTIONS — Corollary 1 run (Lean protocol, Large track)

Project root for this run: `Large Prior\Corollary1\`. The Theorem 1 run's process files in `Large Prior\` are left untouched.

## Gaps and repairs from the proof verdicts (2026-10-14)

Sources: PROOF_VERDICT_FABLE.md (F), PROOF_VERDICT_ASTRA.md (A). Both verdicts: overall **correct up to small changes**. The blueprint will formalize the repaired version.

| G | Issue | Found by | Repair |
|---|---|---|---|
| G1 | Corollary display a_n ≍ (n/log n)^{1/(2α*+d)} is wrong for d ≥ 2 (the proof gives exponent D = d/(2α*+d)). | F, A | Exponent D = d/(2α*+d). |
| G2 | "if s_n ≍ a_n and a_n ≍ …" read as hypotheses makes the d ≥ 2 case vacuous. | F, A | State s_n ≍ a_n, a_n ≍ (n/log n)^D, ε_n ≍ (n/log n)^{-r} as conclusions. |
| G3 | "ε̃_n ↓ 0": monotonicity is not implied (J_n only given up to ≍). | F, A | ε̃_n → 0. |
| G4 | "consequently a_n ≤ J_n" skips the ceiling, C_sp and the ≍ constants. | F, A | a_n/J_n ≍ n^{D−B}(log J_n)^{−D} → 0, B = Σb_k; then 1 ≤ a_n ≤ J_n eventually and ξ*_n can be padded to exactly a_n indices. |
| G5 | Function classes: the generic "anisotropic Hölder ball C^α([0,1]^d)" is undefined for non-integer anisotropic α and unused by the proof; Fourier needs periodicity (counterexample f₀(x) = x, A); splines need α ≤ q, anisotropic splines integer α_k. Section 2.4 sentence and Appendix C overstate coverage. | F, A | Profile is the only function-specific hypothesis of the abstract corollary; list covered (class, dictionary, α-range) pairs separately: splines parts 1–2 (0 < α ≤ q), spline part 3 (integer α_k ≤ q, mixed-derivative class), Fourier (periodic Hölder–Zygmund ball, any α_k > 0). |
| G6 | "the Horseshoe … is admissible" is not proved in the corollary's text. | F, A | Assumption 3 stays a hypothesis of the abstract corollary. (Lead note: the existing Lean theorem `HorseshoeAssumption3Statement` may allow a horseshoe version as a separate result; to be decided in PLAN.md.) |
| G7 | Dual functionals declared on continuous functions, but order-1 splines are discontinuous. | A (F: needs a domain covering sections) | Define the dual functionals on bounded functions (q = 1: midpoint evaluation, C_dual = 1). |
| G8 | Citation provenance: isotropic tensor result for non-integer α is not in Schumaker Thm 6.10 (univariate); Shen–Ghosal Remark 7 states it without proof; anisotropic estimate is Schumaker Thm 12.7 via Shen–Ghosal Lemma 2(a); the manuscript's class uses Σl_k/α_k ≤ 1 vs the reference's < 1. | F, A | Fix citations; for Lean, these classical inputs are a scope decision (see PLAN.md). |
| G9 | Implicit hypotheses: design points in [0,1]^d (splines); f₀ is a periodic function on 𝕋^d (Fourier). | F | Make explicit. |
| G10 | Profile index range should say 1 ≤ m_k ≤ L_{n,k}; the isotropic spline cube conclusion gives the rectangle profile via m = min_k m_k. | A | State both. |
| G11 | "m_{n,k} of the order n^{β_k}" should be (n/log n)^{β_k}. | A | Fix wording. |
| G12 | Notation paragraph: "≍ … coincides with big-O" is wrong. | A | Delete that clause. |

## Modelling decisions (D) — 2026-10-14

| D | Decision | Rejected alternative and reason |
|---|---|---|
| D1 | **Classical inputs as named hypotheses** (choice (a), made by the author): `JacksonIneq` (periodic Jackson–Stechkin), `BSplineReadout` (B-spline sup-norm stability, Schumaker 4.41/de Boor), `SplineOneBlock` / `SplineOneBlockCube` (one-block spline approximation applied to f₀: Schumaker 6.10, 12.7; Shen–Ghosal Lemma 2(a), Remark 7). The spline Hölder classes are not defined in Lean; the classical theorems enter through their conclusion for f₀. The Fourier class (periodic Hölder–Zygmund) is defined, because the proof uses its structure (sections, coordinatewise Jackson). | Defining C^α([0,1]^d) and the anisotropic class in Lean, with the classical theorem as a hypothesis about them: this adds a fidelity risk and no checked content, since the implication would be assumed anyway. Formalizing the classical theorems: option (b), declined by the author. |
| D2 | **Retired 2026-11-03 (cor_v2, W7).** It was: (WG4) assumed for **every** active set S with \|S\| = a_n. Now (WG4) is assumed for one set of size a_n (`CorHyp.h4`). | Reason: `wg4_of_card_eq` (`WG4Perm.lean`) transfers (WG4) to the active set by a coordinate permutation, since the prior is iid; this is the permutation-invariance proof the old row said was missing. |
| D3 | The profile is assumed only for all **sufficiently large** n. | For every n (the paper's literal reading): a stronger hypothesis, so a weaker theorem. |
| D4 | "C_ε sufficiently large" is formalized as C_ε ≥ d·C_app, exactly what the proof uses; Assumption 3 is then assumed for that C_ε. | An existential "some large C_ε": that would hide the dependence of the prior conditions on C_ε. |
| D5 | Constant 5 in (eq:cor1-L1), inherited from the Lean Theorem 1; it implies the paper's 6. | 6: weaker. |
| D6 | The lemmas conclude in **sup-norm** (over ℝ^d for periodic Fourier, over [0,1]^d for splines); the empirical-norm profile follows by a separate transfer lemma (P11). | Empirical-norm-only statements: weaker, and they would mix the design into the lemmas. |
| D7 | Hölder–Zygmund norm ≤ R is written as ∃ A, B ≥ 0 with A + B ≤ R, sup\|f\| ≤ A, and differences ≤ B\|h\|^α. This is equivalent to the norm ≤ R and avoids `sSup` conventions. | `⨆`-based norm: subject to Lean's conventions for unbounded or empty sups. |
| D8 | Real-form Fejér kernel and de la Vallée Poussin operator: (eq:vdp-real) is taken as the definition of V_q (`Qop`), and the kernel identity is proved in real form. | Complex exponentials: more machinery, same operator. |
| D9 | Coefficient bound via ∫₀¹\|ψ\| ≤ ∫₀¹(1 + ψ²)/2 = 1. | ‖ψ‖₁ = 2√2/π: needs ∫\|cos\|, more work, same consequence. |
| D10 | End-to-end sizes: M_{n,k} = ⌈n^{b_k}⌉ (Fourier), H_{n,k} = ⌈b_k log₂ n⌉ (splines). Columns are enumerated by `Fintype.equivFin`. **Revised after Gate A (MAJOR 1):** C_sp and C_ε are chosen before the truth, the design, the exponent b, the prior constants, and c_δ, which is arbitrary in (0,1). | Constants after the design and c_δ = 1/2 (first skeleton): weaker than the manuscript's "independent of the design points". |
| D11 | Horseshoe scale τ_n = J_n^{−(2+μ'')}/√n (c_τ = 1). It does not depend on α, so the prior is adaptive. | A general τ_n with c_τ: no extra generality needed. |
| D12 | The isotropic B-spline end-to-end result uses a common exponent b (equal H_k), matching Lemma part 2 ("H_1 = ⋯ = H_d = H"). | Unequal H_k: the common-level classical input does not cover it. |
| D13 | The tensor readout is derived from the univariate one (section argument), not assumed. | Assuming a tensor readout: more assumed than needed. |
| D14 | Looser constants: 3^d instead of 3^{d−1} (telescoping), ∑_k C'_{α_k} instead of max_k, E = C_dual^d(\|R\| + C⋆d) + 1. | Exact constants: no gain, more arithmetic. |
| D15 | **Univariate Hölder ball defined in Lean for 0 < α ≤ 1** (`HolderBall1`; Gate A MAJOR 2), with the q = 1 one-block property proved for it, so `CorHolderStatement` has no assumed input. Not defined for α > 1, d ≥ 2, or the anisotropic class (D1 stands there). | Defining all the spline classes: for α > 1 the classical implication would still be assumed, so a definition adds fidelity risk without checked content. |
| D16 | `CorConclusion` requires A′ ≥ 1 (literal fidelity to the manuscript's A′ > 0; Astra spec review). | A′ ∈ ℕ unrestricted: harmless but not literal. |
| D17 | Piece splits for size (Gate A MINOR 4, Astra Q4): CorSeqA/CorSeq, TrigBasics/Fejer, VdPBasics/VdP, EndSizes/EndToEnd, CorNonVacuity/CorNonVacuityS. Frozen helper statements added: `sum_range_pair`, `fejerKernel_sumsq`, `Qop_const_mul`, `Qop_finset_sum`, `tendsto_corEpsT`, `nvDesign_mem`, `betaExp_dim_one`, `fejerKernel_le_succ`, `fejerKernel_le_inv_sq`. | One file per original piece: several pieces exceeded one timebox. |

## Changes of 2026-11-03 (frozen `cor_v2`)

- **W2 (explicit constants).** `CorConclusion` states A′ = `corAprime A d Csp Ceps` = A·C_s/C_sp (real) and c = `corExpConst d Csp Ceps` = C_ε²/C_a, with C_a = 2^d C_sp + 1 and C_s = max{C_a, C_ε² + 1} (Appendix B, eq:cor-constants). `CorollaryStatement` uses A = `Aconst K η σ μ c4 c5`, the integer of Theorem 1. The support event uses a real threshold (`denseSetReal`). This supersedes D16 (A′ a natural number ≥ 1): A′ is now a positive real.
- **W4 (Theorem 1 applies).** "Assumption 2 and the standing requirements hold, so that Theorem 1 applies" is exported: `CorTheorem1Inputs` (= Theorem 1's hypotheses `AsymptoticHyp` at the corollary's sequences), proved by `cor_asymptoticHyp` (`CorTheorem1InputsStatement`); it is the first conjunct of `CorollaryStatement`, `CorHorseshoeStatement` and the four end-to-end statements.
- **W7 (D2 retired).** (WG4) is assumed for one set of size a_n (`CorHyp.h4`); `wg4_of_card_eq` (`WG4Perm.lean`) transfers it to the active set ξ*_n by coordinate permutation.
- **W3 (WG5 bridge).** `WG5Bridge.lean`: `wg5_iff_noPos` (for c₅ ≥ 0 the positive part in `WG5` is immaterial) and `wg5Paper_implies_wg5` (the paper's pointwise-infimum (WG5) implies the Lean a.e. `WG5`). The Lean `WG5` is implied by, not equivalent to, the paper's for the horseshoe representative: Lean's `horseshoePDF` is 0 at t = 0, the paper's density is +∞ there.
- **G1 (exponent).** The manuscript now prints D = d/(2α* + d), so the G1 repair now agrees with the paper. The earlier 1/(2α* + d) remark is obsolete.
- **Unchanged.** The classical approximation inputs stay hypotheses on f₀ (D1); the constant 5 (manuscript 6, D5).

## Sign-off

STATEMENTS.md and ASSUMPTIONS.md (frozen v1) approved by the author on 2026-10-14.
