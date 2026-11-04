import LargePrior.WGFixed

/-!
# The horseshoe satisfies Assumption 3 (blueprint `thm:hs-assumption3`)

Translation of Wei and Ghosal (2020), Theorem 3.3.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

noncomputable section

namespace LargePrior

/-- `log x = o(x^ν)`, with coefficient parameter `μ`, for item 2 of the blueprint proof. -/
lemma eventually_two_Lambda_le_split {μ ν K : ℝ} (hμ : 0 < μ) (hν : 0 < ν) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, 2 * ((1 + μ) * Real.log x + Real.log 4) ≤ K * x ^ ν := by
  have h1 := (isLittleO_log_rpow_atTop hν).bound (show 0 < K / (4 * (1 + μ)) by positivity)
  have h2 := (tendsto_rpow_atTop hν).eventually_ge_atTop (2 * 2 * Real.log 4 / K)
  filter_upwards [h1, h2, eventually_ge_atTop 1] with x hx1 hx2 hx3
  have hlog : 0 ≤ Real.log x := Real.log_nonneg hx3
  have hxν : 0 ≤ x ^ ν := Real.rpow_nonneg (by linarith) ν
  rw [Real.norm_of_nonneg hlog, Real.norm_of_nonneg hxν] at hx1
  have h4 : 2 * 2 * Real.log 4 ≤ K * x ^ ν := by
    rw [div_le_iff₀ hK] at hx2; linarith
  have h5 : 2 * (1 + μ) * Real.log x ≤ K / 2 * x ^ ν := by
    calc 2 * (1 + μ) * Real.log x ≤ 2 * (1 + μ) * (K / (4 * (1 + μ)) * x ^ ν) := by gcongr
      _ = K / 2 * x ^ ν := by field_simp; ring
  nlinarith

/-- `log x = o(x^μ)`, in the form used for item 2 of the blueprint proof. -/
private lemma eventually_two_Lambda_le {μ K : ℝ} (hμ : 0 < μ) (hK : 0 < K) :
    ∀ᶠ x : ℝ in atTop, 2 * ((1 + μ) * Real.log x + Real.log 4) ≤ K * x ^ μ :=
  eventually_two_Lambda_le_split hμ hμ hK

/-- `x^{-(2+μ'')} = (x² (x^{μ''/2})²)⁻¹`. -/
private lemma rpow_neg_two_add {x μ'' : ℝ} (hx : 0 < x) :
    x ^ (-(2 + μ'')) = (x ^ 2 * (x ^ (μ'' / 2)) ^ 2)⁻¹ := by
  rw [Real.rpow_neg hx.le, show 2 + μ'' = (2 : ℝ) + μ'' / 2 + μ'' / 2 by ring,
    Real.rpow_add hx, Real.rpow_add hx, Real.rpow_two]
  ring

/-- `x^{-(1+μ)} = (x x^μ)⁻¹`. -/
private lemma rpow_neg_one_add {x μ : ℝ} (hx : 0 < x) :
    x ^ (-(1 + μ)) = (x * x ^ μ)⁻¹ := by
  rw [Real.rpow_neg hx.le, Real.rpow_add hx, Real.rpow_one]

/-- `x^{-(2+(μ+ν))} = (x² x^μ x^ν)⁻¹`. -/
lemma rpow_neg_two_add_split {x μ ν : ℝ} (hx : 0 < x) :
    x ^ (-(2 + (μ + ν))) = (x ^ 2 * x ^ μ * x ^ ν)⁻¹ := by
  rw [Real.rpow_neg hx.le, show 2 + (μ + ν) = (2 : ℝ) + μ + ν by ring,
    Real.rpow_add hx, Real.rpow_add hx, Real.rpow_two]

/-- The tail at `u = min(c_δ, η) ε̃ / J` at a fixed `n`, with target exponent `μ` and the
splitting `μ'' = μ + ν` (blueprint, "Tail at `u_n`"). -/
lemma hs_tail_fixed_mu {J n : ℕ} {εt τ η cδ cτ μ ν : ℝ} (hJ2 : 2 ≤ J) (hn : 1 ≤ n)
    (hnε : 1 ≤ n * εt ^ 2) (hεt : 0 < εt) (hτ : 0 < τ) (hη : 0 < η) (hcδ : 0 < cδ)
    (hcτ : 0 < cτ) (hμ : 0 < μ) (hν : 0 < ν)
    (hΛ : 2 * ((1 + μ) * Real.log J + Real.log 4) ≤
      Real.pi * min cδ η / (4 * cτ) * (J : ℝ) ^ ν)
    (hτJ : τ ≤ cτ * (J : ℝ) ^ (-(2 + (μ + ν))) / Real.sqrt n) :
    coordPrior (horseshoePDF τ) {t | min cδ η * εt / J < |t|} ≤
      ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ))) := by
  have hm0 : 0 < min cδ η := lt_min hcδ hη
  have hx2 : (2 : ℝ) ≤ J := by exact_mod_cast hJ2
  have hx0 : (0 : ℝ) < J := by linarith
  have hP1 : 1 ≤ (J : ℝ) ^ ν := Real.one_le_rpow (by linarith) hν.le
  have hQ0 : 0 < (J : ℝ) ^ μ := Real.rpow_pos_of_pos hx0 μ
  have hlogx : 0 ≤ Real.log J := Real.log_nonneg (by linarith)
  have hlog4 : 1 / 2 ≤ Real.log 4 := by
    have := Real.log_two_gt_d9
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; linarith
  have hΛ1 : 1 ≤ 2 * ((1 + μ) * Real.log J + Real.log 4) := by
    have : 0 ≤ (1 + μ) * Real.log J := by positivity
    linarith
  set Λ := (1 + μ) * Real.log J + Real.log 4 with hΛdef
  set P := (J : ℝ) ^ ν with hP
  set Q := (J : ℝ) ^ μ with hQ
  set K := Real.pi * min cδ η / (4 * cτ) with hK
  have hs0 : 0 < Real.sqrt (2 * Λ) := Real.sqrt_pos.mpr (by linarith)
  have hsq : Real.sqrt (2 * Λ) ≤ K * P := by
    rw [Real.sqrt_le_iff]
    constructor
    · linarith
    · nlinarith
  have hsn : 1 ≤ Real.sqrt n := by
    rw [Real.one_le_sqrt]; exact_mod_cast hn
  have hεsn : 1 ≤ εt * Real.sqrt n := by
    have h1 : (εt * Real.sqrt n) ^ 2 = n * εt ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; ring
    have h2 : 0 ≤ εt * Real.sqrt n := by positivity
    nlinarith
  have hu : 0 < min cδ η * εt / J := by positivity
  apply horseshoe_tail_le_J hτ hu hJ2 hμ
  rw [rpow_neg_one_add hx0, le_div_iff₀ hs0]
  rw [rpow_neg_two_add_split hx0] at hτJ
  have hsn0 : 0 < Real.sqrt n := by linarith
  have hP0 : 0 < P := by linarith
  have hK0 : 0 < K := by positivity
  calc τ * Real.sqrt (2 * Λ) ≤ cτ * ((J : ℝ) ^ 2 * Q * P)⁻¹ / Real.sqrt n * (K * P) :=
        mul_le_mul hτJ hsq hs0.le (by positivity)
    _ = Real.pi * min cδ η / (4 * (J : ℝ) ^ 2 * Q) * (1 / Real.sqrt n) := by
        rw [hK]; field_simp
    _ ≤ Real.pi * min cδ η / (4 * (J : ℝ) ^ 2 * Q) * εt := by
        gcongr
        rw [div_le_iff₀ hsn0]; linarith
    _ = Real.pi / 4 * (min cδ η * εt / J * (J * Q)⁻¹) := by
        field_simp

/-- The tail at `u = min(c_δ, η) ε̃ / J` at a fixed `n` (blueprint, "Tail at `u_n`"). -/
private lemma hs_tail_fixed {J n : ℕ} {εt τ η cδ cτ μ'' : ℝ} (hJ2 : 2 ≤ J) (hn : 1 ≤ n)
    (hnε : 1 ≤ n * εt ^ 2) (hεt : 0 < εt) (hτ : 0 < τ) (hη : 0 < η) (hcδ : 0 < cδ)
    (hcτ : 0 < cτ) (hμ'' : 0 < μ'')
    (hΛ : 2 * ((1 + μ'' / 2) * Real.log J + Real.log 4) ≤
      Real.pi * min cδ η / (4 * cτ) * (J : ℝ) ^ (μ'' / 2))
    (hτJ : τ ≤ cτ * (J : ℝ) ^ (-(2 + μ'')) / Real.sqrt n) :
    coordPrior (horseshoePDF τ) {t | min cδ η * εt / J < |t|} ≤
      ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ'' / 2))) := by
  have hμ0 : 0 < μ'' / 2 := by positivity
  exact hs_tail_fixed_mu hJ2 hn hnε hεt hτ hη hcδ hcτ hμ0 hμ0 hΛ (by rwa [add_halves])

/-- (WG5) budget at a fixed `n` with `c₅ = B(6 + 5B)` (blueprint, "(WG5) with `c₅`"). -/
private lemma hs_wg5_budget {J n a : ℕ} {εt E τ B : ℝ} (hJ2 : 2 ≤ J) (ha1 : 1 ≤ a)
    (haJ : a ≤ J) (hτ : 0 < τ) (hτ1 : τ ≤ 1) (hE : 0 < E) (hB : 0 ≤ B)
    (hb1 : (a : ℝ) * Real.log J ≤ B * n * εt ^ 2) (hb2 : Real.log (1 / εt) ≤ B * Real.log J)
    (hb3 : Real.log (1 / τ) ≤ B * Real.log J) (hb4 : Real.log E ≤ B * Real.log J) :
    (a : ℝ) * max 0 (Real.log a + 2 * Real.log (1 / εt) -
        Real.log (hsConst * τ / max E τ ^ 2)) ≤ B * (6 + 5 * B) * n * εt ^ 2 := by
  have hℓ : Real.log 2 ≤ Real.log J :=
    Real.log_le_log (by norm_num) (by exact_mod_cast hJ2)
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hhs0 : 0 < hsConst := lt_of_lt_of_le (by norm_num) hsConst_ge
  have hM0 : 0 < max E τ := lt_max_of_lt_left hE
  have hsplit : Real.log (hsConst * τ / max E τ ^ 2) =
      Real.log hsConst + Real.log τ - 2 * Real.log (max E τ) := by
    rw [Real.log_div (by positivity) (by positivity), Real.log_mul hhs0.ne' hτ.ne',
      Real.log_pow]
    push_cast; ring
  have hhs : -(5 * Real.log 2) ≤ Real.log hsConst := by
    have h1 : Real.log (1 / 32) ≤ Real.log hsConst := Real.log_le_log (by norm_num) hsConst_ge
    have h32 : Real.log (1 / 32 : ℝ) = -(5 * Real.log 2) := by
      rw [one_div, Real.log_inv, show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      push_cast; ring
    linarith
  have hτlog : -Real.log τ ≤ B * Real.log J := by
    rw [one_div, Real.log_inv] at hb3; exact hb3
  have hτ0 : Real.log τ ≤ 0 := Real.log_nonpos hτ.le hτ1
  have hBℓ : 0 ≤ B * Real.log J := mul_nonneg hB (by linarith)
  have hmax : Real.log (max E τ) ≤ B * Real.log J := by
    rcases le_total E τ with h | h
    · rw [max_eq_right h]; linarith
    · rw [max_eq_left h]; exact hb4
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hloga : Real.log a ≤ Real.log J := Real.log_le_log ha0 (by exact_mod_cast haJ)
  have hX : Real.log a + 2 * Real.log (1 / εt) - Real.log (hsConst * τ / max E τ ^ 2) ≤
      (6 + 5 * B) * Real.log J := by
    rw [hsplit]; nlinarith
  have hℓ0 : 0 ≤ Real.log J := by linarith
  have hmax0 : max 0 (Real.log a + 2 * Real.log (1 / εt) -
      Real.log (hsConst * τ / max E τ ^ 2)) ≤ (6 + 5 * B) * Real.log J :=
    max_le (by positivity) hX
  calc (a : ℝ) * max 0 (Real.log a + 2 * Real.log (1 / εt) -
        Real.log (hsConst * τ / max E τ ^ 2))
      ≤ a * ((6 + 5 * B) * Real.log J) := mul_le_mul_of_nonneg_left hmax0 ha0.le
    _ = (6 + 5 * B) * (a * Real.log J) := by ring
    _ ≤ (6 + 5 * B) * (B * n * εt ^ 2) := mul_le_mul_of_nonneg_left hb1 (by positivity)
    _ = B * (6 + 5 * B) * n * εt ^ 2 := by ring

/-- All three conclusions at a fixed `n`, with target exponent `μ` and `μ'' = μ + ν`. -/
lemma hs_fixed_mu {J n a : ℕ} {εt δ E τ η μ ν cδ cτ B : ℝ} (hJ2 : 2 ≤ J) (hn : 1 ≤ n)
    (hnε : 1 ≤ n * εt ^ 2) (hη : 0 < η) (hμ : 0 < μ) (hν : 0 < ν) (hcδ : 0 < cδ) (hcτ : 0 < cτ)
    (hB : 0 ≤ B) (hQ : 2 ≤ (J : ℝ) ^ μ) (hP : max 2 cτ ≤ (J : ℝ) ^ ν)
    (hΛ : 2 * ((1 + μ) * Real.log J + Real.log 4) ≤
      Real.pi * min cδ η / (4 * cτ) * (J : ℝ) ^ ν)
    (ha : 1 ≤ a ∧ a ≤ J) (hεt : 0 < εt) (hE : 0 < E) (hτ : 0 < τ)
    (hδ : cδ * εt / J ≤ δ) (hτJ : τ ≤ cτ * (J : ℝ) ^ (-(2 + (μ + ν))) / Real.sqrt n)
    (hb : (a : ℝ) * Real.log J ≤ B * n * εt ^ 2 ∧ Real.log (1 / εt) ≤ B * Real.log J ∧
      Real.log (1 / τ) ≤ B * Real.log J ∧ Real.log E ≤ B * Real.log J) :
    WG3 (horseshoePDF τ) δ μ J ∧
      (∀ S : Finset (Fin J), S.card = a → WG4 (horseshoePDF τ) J S η εt 1 n) ∧
      WG5 (horseshoePDF τ) E εt (B * (6 + 5 * B)) a n := by
  have htail := hs_tail_fixed_mu hJ2 hn hnε hεt hτ hη hcδ hcτ hμ hν hΛ hτJ
  have hx0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  refine ⟨?_, ?_, ?_⟩
  · refine wg3_of_tail (le_trans ?_ hδ) htail
    gcongr
    exact min_le_left _ _
  · -- The tail bound gives WG4 for every active set, independently of its cardinality.
    intro S _
    have hsub : {t : ℝ | η * εt / J < |t|} ⊆ {t : ℝ | min cδ η * εt / J < |t|} := by
      intro t (ht : η * εt / J < |t|)
      show min cδ η * εt / J < |t|
      refine lt_of_le_of_lt ?_ ht
      gcongr
      exact min_le_right _ _
    have hc4 : Real.log 2 ≤ 1 * n * εt ^ 2 := by
      have := Real.log_two_lt_d9
      linarith
    exact wg4_of_tail (horseshoe_isProbDensity τ hτ) hJ2 (by positivity)
      hQ hη hεt hc4 ((measure_mono hsub).trans htail) S
  · have hτ1 : τ ≤ 1 := by
      rw [rpow_neg_two_add_split hx0] at hτJ
      have hsn : 1 ≤ Real.sqrt n := by
        rw [Real.one_le_sqrt]; exact_mod_cast hn
      have hx2 : (2 : ℝ) ≤ J := by exact_mod_cast hJ2
      set P := (J : ℝ) ^ ν
      have hP2 : 2 ≤ P := (le_max_left _ _).trans hP
      have hPc : cτ ≤ P := (le_max_right _ _).trans hP
      have hP0 : 0 < P := by linarith
      have hPJ : P ≤ (J : ℝ) ^ 2 * (J : ℝ) ^ μ * P := by
        have h1 : 1 ≤ (J : ℝ) ^ 2 * (J : ℝ) ^ μ := by nlinarith
        exact le_mul_of_one_le_left hP0.le h1
      have hden : cτ ≤ (J : ℝ) ^ 2 * (J : ℝ) ^ μ * P := hPc.trans hPJ
      refine hτJ.trans ?_
      rw [div_le_one (by linarith), ← div_eq_mul_inv]
      exact ((div_le_one (by positivity)).mpr hden).trans hsn
    obtain ⟨hb1, hb2, hb3, hb4⟩ := hb
    exact horseshoe_wg5 hτ hE (hs_wg5_budget hJ2 ha.1 ha.2 hτ hτ1 hE hB hb1 hb2 hb3 hb4)

/-- All three conclusions at a fixed `n`, from the eventual numeric facts. -/
private lemma hs_fixed {J n a : ℕ} {εt δ E τ η μ'' cδ cτ B : ℝ} (hJ2 : 2 ≤ J) (hn : 1 ≤ n)
    (hnε : 1 ≤ n * εt ^ 2) (hη : 0 < η) (hμ'' : 0 < μ'') (hcδ : 0 < cδ) (hcτ : 0 < cτ)
    (hB : 0 ≤ B) (hP : max 2 cτ ≤ (J : ℝ) ^ (μ'' / 2))
    (hΛ : 2 * ((1 + μ'' / 2) * Real.log J + Real.log 4) ≤
      Real.pi * min cδ η / (4 * cτ) * (J : ℝ) ^ (μ'' / 2))
    (ha : 1 ≤ a ∧ a ≤ J) (hεt : 0 < εt) (hE : 0 < E) (hτ : 0 < τ)
    (hδ : cδ * εt / J ≤ δ) (hτJ : τ ≤ cτ * (J : ℝ) ^ (-(2 + μ'')) / Real.sqrt n)
    (hb : (a : ℝ) * Real.log J ≤ B * n * εt ^ 2 ∧ Real.log (1 / εt) ≤ B * Real.log J ∧
      Real.log (1 / τ) ≤ B * Real.log J ∧ Real.log E ≤ B * Real.log J) :
    WG3 (horseshoePDF τ) δ (μ'' / 2) J ∧
      (∀ S : Finset (Fin J), S.card = a → WG4 (horseshoePDF τ) J S η εt 1 n) ∧
      WG5 (horseshoePDF τ) E εt (B * (6 + 5 * B)) a n := by
  have hμ0 : 0 < μ'' / 2 := by positivity
  exact hs_fixed_mu hJ2 hn hnε hη hμ0 hμ0 hcδ hcτ hB ((le_max_left _ _).trans hP) hP hΛ ha hεt hE
    hτ hδ (by rwa [add_halves]) hb

/-- **The horseshoe prior with a deterministic global scale satisfies (WG3)–(WG5).** -/
theorem horseshoe_assumption3 : HorseshoeAssumption3Statement := by
  intro J εt δ E τ a η μ'' cδ cτ B hJ hnεt hη hμ'' hcδ hcτ hB ha hεt hE hτ hδ hτJ hbud
  have hJR : Tendsto (fun n => (J n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop.comp hJ
  have hμ : 0 < μ'' / 2 := by positivity
  have hK : 0 < Real.pi * min cδ η / (4 * cτ) := by
    have := lt_min hcδ hη
    positivity
  have hP : Tendsto (fun n => (J n : ℝ) ^ (μ'' / 2)) atTop atTop :=
    (tendsto_rpow_atTop hμ).comp hJR
  filter_upwards [hJ.eventually_ge_atTop 2, eventually_ge_atTop 1, hnεt.eventually_ge_atTop 1,
    hP.eventually_ge_atTop (max 2 cτ), hJR.eventually (eventually_two_Lambda_le hμ hK),
    ha, hεt, hE, hτ, hδ, hτJ, hbud] with n hJ2 hn1 hnε hPn hΛ han hεn hEn hτn hδn hτJn hbn
  exact hs_fixed hJ2 hn1 hnε hη hμ'' hcδ hcτ hB hPn hΛ han hεn hEn hτn hδn hτJn hbn

end LargePrior
