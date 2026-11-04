import LargePrior.HorseshoeAsymptotic

/-!
# The horseshoe paragraph of the paper (v3: W1, W5)

The paper (Section 2, after Theorem 1) states: if, for a constant `μ' > 0`,
`τ_n ≤ J_n^{−(2+μ')}/√n`, `−log τ_n = O(log J_n)`, `log E_n = O(log J_n)`, `δ_n ≍ ε̃_n/J_n`,
`a_n log J_n ≲ n ε̃_n²` and `n ε̃_n²/log J_n → ∞` (eq:hs-conditions), then the horseshoe with the
deterministic global scale `τ_n` satisfies Assumption 3, **with any `μ < μ'` in (WG3)**.

* `HorseshoeAssumption3MuStatement` generalizes the frozen `HorseshoeAssumption3Statement`
  (which fixes `μ = μ''/2`) to every `μ ∈ (0, μ'')`.
* `HorseshoePaperConditionsStatement` is the paragraph itself: the conditions of
  eq:hs-conditions, with explicit `O`-constants (one-sided, which is weaker), imply that there is
  `c₅ ≥ 0` such that for every `μ ∈ (0, μ')`, for all large `n`: (WG3) with `μ`, (WG4) with
  `c₄ = 1` for every set of size `a_n`, and (WG5) with `c₅`. Only the lower half
  `c_δ ε̃_n/J_n ≤ δ_n` of `δ_n ≍ ε̃_n/J_n` is needed (the upper half is Theorem 1's standing
  requirement), and only `η > 0`.

(WG5) is the Lean `WG5`: an almost-everywhere lower bound on `[−E_n, E_n]`. The paper's density
is `+∞` at `0`, so its pointwise infimum equals the infimum over `t ≠ 0`; Lean's `horseshoePDF`
takes the value `0` at `t = 0` (a null set), and `horseshoe_lower` gives the pointwise bound for
every `t ≠ 0`.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

noncomputable section

namespace LargePrior

/-- **Wei–Ghosal Theorem 3.3 for the horseshoe, with any `μ ∈ (0, μ'')` in (WG3).** Same
hypotheses as `HorseshoeAssumption3Statement`, plus `0 < μ < μ''`; conclusion (WG3) with this
`μ`, (WG4) with `c₄ = 1` for every active set of size `a_n`, and (WG5) with `c₅ = B(6 + 5B)` (in
the almost-everywhere form of `WG5`), for all sufficiently large `n`. -/
def HorseshoeAssumption3MuStatement : Prop :=
  ∀ (J : ℕ → ℕ) (εt δ E τ : ℕ → ℝ) (a : ℕ → ℕ) (η μ μ'' cδ cτ B : ℝ),
    Tendsto J atTop atTop → Tendsto (fun n : ℕ => (n : ℝ) * εt n ^ 2) atTop atTop →
    0 < η → 0 < μ → μ < μ'' → 0 < cδ → 0 < cτ → 0 ≤ B →
    (∀ᶠ n in atTop, 1 ≤ a n ∧ a n ≤ J n) →
    (∀ᶠ n in atTop, 0 < εt n) → (∀ᶠ n in atTop, 0 < E n) → (∀ᶠ n in atTop, 0 < τ n) →
    (∀ᶠ n in atTop, cδ * εt n / J n ≤ δ n) →
    (∀ᶠ n in atTop, τ n ≤ cτ * (J n : ℝ) ^ (-(2 + μ'')) / Real.sqrt n) →
    (∀ᶠ n in atTop, (a n : ℝ) * Real.log (J n) ≤ B * n * εt n ^ 2 ∧
        Real.log (1 / εt n) ≤ B * Real.log (J n) ∧
        Real.log (1 / τ n) ≤ B * Real.log (J n) ∧
        Real.log (E n) ≤ B * Real.log (J n)) →
    ∀ᶠ n in atTop,
      WG3 (horseshoePDF (τ n)) (δ n) μ (J n) ∧
      (∀ S : Finset (Fin (J n)), S.card = a n → WG4 (horseshoePDF (τ n)) (J n) S η (εt n) 1 n) ∧
      WG5 (horseshoePDF (τ n)) (E n) (εt n) (B * (6 + 5 * B)) (a n) n

/-- **The paper's horseshoe paragraph** (eq:hs-conditions ⇒ Assumption 3, with any `μ < μ'`
in (WG3)): if `J_n → ∞`, `n ε̃_n²/log J_n → ∞`, `1 ≤ a_n ≤ J_n`, `ε̃_n, E_n, τ_n > 0`,
`τ_n ≤ J_n^{−(2+μ')}/√n`, `−log τ_n ≤ C_τ log J_n`, `log E_n ≤ C_E log J_n`,
`c_δ ε̃_n/J_n ≤ δ_n` and `a_n log J_n ≤ C_a n ε̃_n²` for all large `n`, then there is `c₅ ≥ 0`
such that for every `μ ∈ (0, μ')`, for all large `n`, the horseshoe with scale `τ_n` satisfies
(WG3) with `μ`, (WG4) with `c₄ = 1` for every set of size `a_n`, and (WG5) with `c₅` (in the
almost-everywhere form of `WG5`). -/
def HorseshoePaperConditionsStatement : Prop :=
  ∀ (J : ℕ → ℕ) (εt δ E τ : ℕ → ℝ) (a : ℕ → ℕ) (η μ' cδ Cτ CE Ca : ℝ),
    Tendsto J atTop atTop →
    Tendsto (fun n : ℕ => (n : ℝ) * εt n ^ 2 / Real.log (J n)) atTop atTop →
    0 < η → 0 < μ' → 0 < cδ →
    (∀ᶠ n in atTop, 1 ≤ a n ∧ a n ≤ J n) →
    (∀ᶠ n in atTop, 0 < εt n) → (∀ᶠ n in atTop, 0 < E n) → (∀ᶠ n in atTop, 0 < τ n) →
    (∀ᶠ n in atTop, τ n ≤ (J n : ℝ) ^ (-(2 + μ')) / Real.sqrt n) →
    (∀ᶠ n in atTop, -Real.log (τ n) ≤ Cτ * Real.log (J n)) →
    (∀ᶠ n in atTop, Real.log (E n) ≤ CE * Real.log (J n)) →
    (∀ᶠ n in atTop, cδ * εt n / J n ≤ δ n) →
    (∀ᶠ n in atTop, (a n : ℝ) * Real.log (J n) ≤ Ca * n * εt n ^ 2) →
    ∃ c5 : ℝ, 0 ≤ c5 ∧ ∀ μ : ℝ, 0 < μ → μ < μ' →
      ∀ᶠ n in atTop,
        WG3 (horseshoePDF (τ n)) (δ n) μ (J n) ∧
        (∀ S : Finset (Fin (J n)), S.card = a n →
          WG4 (horseshoePDF (τ n)) (J n) S η (εt n) 1 n) ∧
        WG5 (horseshoePDF (τ n)) (E n) (εt n) c5 (a n) n

/-- **Wei–Ghosal Theorem 3.3 with any `μ ∈ (0, μ'')`** (W1). -/
theorem horseshoe_assumption3_mu : HorseshoeAssumption3MuStatement := by
  intro J εt δ E τ a η μ μ'' cδ cτ B hJ hnεt hη hμ hμμ'' hcδ hcτ hB ha hεt hE hτ hδ hτJ hbud
  have hJR : Tendsto (fun n => (J n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hJ
  have hν : 0 < μ'' - μ := sub_pos.mpr hμμ''
  have hK : 0 < Real.pi * min cδ η / (4 * cτ) := by
    have := lt_min hcδ hη
    positivity
  have hP : Tendsto (fun n => (J n : ℝ) ^ (μ'' - μ)) atTop atTop :=
    (tendsto_rpow_atTop hν).comp hJR
  have hQ : Tendsto (fun n => (J n : ℝ) ^ μ) atTop atTop :=
    (tendsto_rpow_atTop hμ).comp hJR
  filter_upwards [hJ.eventually_ge_atTop 2, eventually_ge_atTop 1, hnεt.eventually_ge_atTop 1,
    hQ.eventually_ge_atTop 2, hP.eventually_ge_atTop (max 2 cτ),
    hJR.eventually (eventually_two_Lambda_le_split hμ hν hK),
    ha, hεt, hE, hτ, hδ, hτJ, hbud] with n hJ2 hn1 hnε hQn hPn hΛ han hεn hEn hτn hδn hτJn hbn
  have hτJ' : τ n ≤ cτ * (J n : ℝ) ^ (-(2 + (μ + (μ'' - μ)))) / Real.sqrt n := by
    rwa [add_sub_cancel]
  exact hs_fixed_mu hJ2 hn1 hnε hη hμ hν hcδ hcτ hB hQn hPn hΛ han hεn hEn hτn hδn hτJ' hbn

/-- **The paper's horseshoe paragraph** (W5). -/
theorem horseshoe_paper_conditions : HorseshoePaperConditionsStatement := by
  intro J εt δ E τ a η μ' cδ Cτ CE Ca hJ hrat hη hμ' hcδ ha hεt hE hτ hτle hCτ hCE hδ hCa
  set B : ℝ := max (max Ca Cτ) (max CE 0) with hBdef
  have hB0 : 0 ≤ B := le_trans (le_max_right CE 0) (le_max_right _ _)
  have hCaB : Ca ≤ B := le_trans (le_max_left Ca Cτ) (le_max_left _ _)
  have hCτB : Cτ ≤ B := le_trans (le_max_right Ca Cτ) (le_max_left _ _)
  have hCEB : CE ≤ B := le_trans (le_max_left CE 0) (le_max_right _ _)
  refine ⟨B * (6 + 5 * B), by positivity, ?_⟩
  intro μ hμ hμμ'
  -- J large, so log J ≥ 1
  have hJ3 : ∀ᶠ n in atTop, 3 ≤ J n := hJ.eventually (eventually_ge_atTop 3)
  have hlog1 : ∀ᶠ n in atTop, 1 ≤ Real.log (J n) := by
    filter_upwards [hJ3] with n hn
    have h3 : (3 : ℝ) ≤ (J n : ℝ) := by exact_mod_cast hn
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hnε : Tendsto (fun n : ℕ => (n : ℝ) * εt n ^ 2) atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ hrat
    filter_upwards [hlog1] with n hn
    exact div_le_self (by positivity) hn
  have hnε1 : ∀ᶠ n : ℕ in atTop, 1 ≤ (n : ℝ) * εt n ^ 2 := hnε.eventually (eventually_ge_atTop 1)
  have hbudget : ∀ᶠ n : ℕ in atTop, (a n : ℝ) * Real.log (J n) ≤ B * n * εt n ^ 2 ∧
        Real.log (1 / εt n) ≤ B * Real.log (J n) ∧
        Real.log (1 / τ n) ≤ B * Real.log (J n) ∧
        Real.log (E n) ≤ B * Real.log (J n) := by
    filter_upwards [hlog1, hnε1, hεt, hτ, hτle, hCτ, hCE, hCa, hJ3] with n h1 hn1 hεn hτn hτn' hCτn hCEn hCan hJ3n
    have hL0 : 0 ≤ Real.log (J n) := by linarith
    have hJpos : (0 : ℝ) < (J n : ℝ) := by
      have : (3 : ℝ) ≤ (J n : ℝ) := by exact_mod_cast hJ3n
      linarith
    have hnpos : (0 : ℝ) < (n : ℝ) := by
      rcases Nat.eq_zero_or_pos n with h | h
      · subst h; exfalso; norm_num at hn1
      · exact_mod_cast h
    -- Active-coordinate budget.
    have c1 : (a n : ℝ) * Real.log (J n) ≤ B * n * εt n ^ 2 := by
      have hx : 0 ≤ (n : ℝ) * εt n ^ 2 := by positivity
      calc (a n : ℝ) * Real.log (J n) ≤ Ca * n * εt n ^ 2 := hCan
        _ = Ca * ((n : ℝ) * εt n ^ 2) := by ring
        _ ≤ B * ((n : ℝ) * εt n ^ 2) := mul_le_mul_of_nonneg_right hCaB hx
        _ = B * n * εt n ^ 2 := by ring
    -- log τ upper bound
    have hlogτ : Real.log (τ n) ≤ -(2 + μ') * Real.log (J n) - 1 / 2 * Real.log (n : ℝ) := by
      have h := Real.log_le_log hτn hτn'
      rw [Real.log_div (by positivity) (by positivity), Real.log_rpow hJpos,
        Real.log_sqrt hnpos.le] at h
      linarith
    have hhalf : 1 / 2 * Real.log (n : ℝ) ≤ Cτ * Real.log (J n) := by
      nlinarith only [hlogτ, hCτn, hL0, mul_nonneg hμ'.le hL0]
    -- Inverse-radius budget, via n ε̃² ≥ 1.
    have hε2 : -Real.log (εt n) ≤ 1 / 2 * Real.log (n : ℝ) := by
      have h := Real.log_le_log one_pos hn1
      rw [Real.log_one, Real.log_mul hnpos.ne' (by positivity), Real.log_pow] at h
      push_cast at h
      linarith
    have c2 : Real.log (1 / εt n) ≤ B * Real.log (J n) := by
      rw [one_div, Real.log_inv]
      exact hε2.trans (hhalf.trans (mul_le_mul_of_nonneg_right hCτB hL0))
    -- Inverse-scale budget.
    have c3 : Real.log (1 / τ n) ≤ B * Real.log (J n) := by
      rw [one_div, Real.log_inv]
      exact hCτn.trans (mul_le_mul_of_nonneg_right hCτB hL0)
    -- Envelope budget.
    have c4 : Real.log (E n) ≤ B * Real.log (J n) := by
      exact hCEn.trans (mul_le_mul_of_nonneg_right hCEB hL0)
    exact ⟨c1, c2, c3, c4⟩
  have hτle' : ∀ᶠ n in atTop, τ n ≤ 1 * (J n : ℝ) ^ (-(2 + μ')) / Real.sqrt n := by
    filter_upwards [hτle] with n hn
    rw [one_mul]; exact hn
  exact horseshoe_assumption3_mu J εt δ E τ a η μ μ' cδ 1 B hJ hnε hη hμ hμμ' hcδ one_pos hB0
    ha hεt hE hτ hδ hτle' hbudget

/-- The frozen `HorseshoeAssumption3Statement` is the instance `μ = μ''/2` of
`HorseshoeAssumption3MuStatement`. -/
theorem horseshoe_assumption3_of_mu : HorseshoeAssumption3Statement := by
  intro J εt δ E τ a η μ'' cδ cτ B hJ hnεt hη hμ'' hcδ hcτ hB ha hεt hE hτ hδ hτJ hbud
  have hμ0 : 0 < μ'' / 2 := by positivity
  exact horseshoe_assumption3_mu J εt δ E τ a η (μ'' / 2) μ'' cδ cτ B hJ hnεt hη hμ0
    (by linarith) hcδ hcτ hB ha hεt hE hτ hδ hτJ hbud

end LargePrior
