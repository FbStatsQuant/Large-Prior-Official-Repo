import LargePrior.Master

/-!
# Theorem 1 as stated in the paper (`thm:main`)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

/-- `ε̃² ≤ s log J / n`, from the definition of `s`. -/
private lemma sq_le_sRate_mul_log {n J a : ℕ} {εt : ℝ} (hn : 0 < n) (hJ : 2 ≤ J) :
    εt ^ 2 ≤ (sRate n J a εt : ℝ) * Real.log J / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hJR : (2 : ℝ) ≤ J := by exact_mod_cast hJ
  have hlog : 0 < Real.log J := Real.log_pos (by linarith)
  have h1 : (n : ℝ) * εt ^ 2 / Real.log J ≤ (sRate n J a εt : ℝ) :=
    (Nat.le_ceil _).trans (by
      have : ⌈(n : ℝ) * εt ^ 2 / Real.log J⌉₊ ≤ sRate n J a εt := le_max_right _ _
      exact_mod_cast this)
  rw [div_le_iff₀ hlog] at h1
  rw [le_div_iff₀ hnR]
  linarith

/-- Eventually `ε̃ ≤ η`. -/
private lemma eventually_epsilon_le_eta {J : ℕ → ℕ} {X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ}
    {f₀ : ∀ n : ℕ, Fin n → ℝ} {σ : ℝ} {pdf : ℕ → ℝ → ℝ} {εt δ E M : ℕ → ℝ} {a : ℕ → ℕ}
    {K η μ c4 c5 : ℝ} (h : AsymptoticHyp J X f₀ σ pdf εt δ E M a K η μ c4 c5) :
    ∀ᶠ n in atTop, 0 < n → 2 ≤ J n → 0 < εt n → εt n ≤ η := by
  have hs : ∀ᶠ n in atTop,
      (sRate n (J n) (a n) (εt n) : ℝ) * Real.log (J n) / n < η ^ 2 :=
    h.hs.eventually (gt_mem_nhds (by have := h.hη; positivity))
  filter_upwards [hs] with n hn hn0 hJ hε
  have h1 := sq_le_sRate_mul_log (a := a n) (εt := εt n) hn0 hJ
  have h2 : εt n ^ 2 < η ^ 2 := lt_of_le_of_lt h1 hn
  have hη := h.hη
  by_contra hcon
  push Not at hcon
  nlinarith

/-- Eventual lower bounds on `J n`. -/
private lemma eventually_J_facts {J : ℕ → ℕ} {μ : ℝ} (hμ : 0 < μ)
    (hJ : Tendsto J atTop atTop) :
    ∀ᶠ n in atTop, 2 ≤ J n ∧ 2 ≤ (J n : ℝ) ^ μ ∧ 1 + Real.log 97 ≤ Real.log (J n) := by
  have hR : Tendsto (fun n => (J n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hJ
  have h1 : ∀ᶠ n in atTop, 2 ≤ J n := hJ.eventually_ge_atTop 2
  have h2 : ∀ᶠ n in atTop, 2 ≤ (J n : ℝ) ^ μ :=
    ((tendsto_rpow_atTop hμ).comp hR).eventually_ge_atTop 2
  have h3 : ∀ᶠ n in atTop, 1 + Real.log 97 ≤ Real.log (J n) :=
    (Real.tendsto_log_atTop.comp hR).eventually_ge_atTop _
  filter_upwards [h1, h2, h3] with n a b c using ⟨a, b, c⟩

/-- Eventual lower bounds on `M n`. -/
private lemma eventually_M_facts {M : ℕ → ℝ} (hM : Tendsto M atTop atTop) (r1 r2 r3 : ℝ) :
    ∀ᶠ n in atTop, r1 ≤ M n ∧ r2 ≤ M n ^ 2 ∧ r3 ≤ M n ^ 2 := by
  have h1 := hM.eventually_ge_atTop r1
  have h2 := hM.eventually_ge_atTop (max 1 r2)
  have h3 := hM.eventually_ge_atTop (max 1 r3)
  filter_upwards [h1, h2, h3] with n a b c
  refine ⟨a, ?_, ?_⟩
  · have b1 : 1 ≤ M n := (le_max_left _ _).trans b
    have b2 : r2 ≤ M n := (le_max_right _ _).trans b
    nlinarith
  · have b1 : 1 ≤ M n := (le_max_left _ _).trans c
    have b2 : r3 ≤ M n := (le_max_right _ _).trans c
    nlinarith

/-- The hypotheses of the master theorem hold for all sufficiently large `n`. -/
theorem eventually_masterHyp {J : ℕ → ℕ} {X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ}
    {f₀ : ∀ n : ℕ, Fin n → ℝ} {σ : ℝ} {pdf : ℕ → ℝ → ℝ} {εt δ E M : ℕ → ℝ} {a : ℕ → ℕ}
    {K η μ c4 c5 : ℝ} (h : AsymptoticHyp J X f₀ σ pdf εt δ E M a K η μ c4 c5) :
    ∀ᶠ n in atTop,
      MasterHyp n (J n) σ (X n) (f₀ n) (pdf n) (εt n) (δ n) (E n) (M n) (a n) K η μ c4 c5 := by
  have hn1 : ∀ᶠ n : ℕ in atTop, 0 < n := eventually_gt_atTop 0
  have hJf := eventually_J_facts h.hμ h.hJ
  have hlog2 : ∀ᶠ n : ℕ in atTop, Real.log 2 ≤ n * εt n ^ 2 :=
    h.hnεt.eventually_ge_atTop _
  have hMf := eventually_M_facts h.hM (16 * K) (16 * σ ^ 2 * (2 * (Aconst K η σ μ c4 c5 : ℝ) + 1))
    (64 * σ ^ 2 * (C1 K η σ c4 c5 + 1))
  have hη := eventually_epsilon_le_eta h
  filter_upwards [hn1, hJf, hlog2, hMf, hη, h.hpdf, h.hεt, h.hδ, h.hE, h.ha, h.hδεt, h.hbasis,
    h.hA2, h.h3, h.h5] with n hn ⟨hJ2, hJμ, hJl⟩ hl ⟨hM5, hM6, hM7⟩ hηn hpdf hεt hδ hE ha hδεt
    hbasis hA2 h3 h5
  exact ⟨hn, hJ2, h.hσ, hpdf, hεt, hδ, hE, ha.1, ha.2, h.hK, h.hη, h.hμ, h.hc4, h.hc5, hδεt,
    hbasis, hA2, h3, h5, hηn hn hJ2 hεt, hJμ, hl, hJl, hM5, hM6, hM7⟩

/-- Markov's inequality along a sequence. -/
lemma tendsto_measure_gt_of_lintegral_le {Z : ∀ n : ℕ, (Fin n → ℝ) → ℝ≥0∞}
    {P : ∀ n : ℕ, Measure (Fin n → ℝ)} (hZ : ∀ᶠ n in atTop, Measurable (Z n)) {b : ℕ → ℝ}
    (hb : Tendsto b atTop (𝓝 0))
    (hle : ∀ᶠ n in atTop, ∫⁻ y, Z n y ∂(P n) ≤ ENNReal.ofReal (b n)) {ζ : ℝ} (hζ : 0 < ζ) :
    Tendsto (fun n => P n {y | ENNReal.ofReal ζ < Z n y}) atTop (𝓝 0) := by
  have hε0 : ENNReal.ofReal ζ ≠ 0 := by simpa using hζ
  have hεtop : ENNReal.ofReal ζ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hb' : Tendsto (fun n => ENNReal.ofReal (b n)) atTop (𝓝 0) := by
    simpa using (ENNReal.tendsto_ofReal hb)
  have hup : Tendsto (fun n => ENNReal.ofReal (b n) / ENNReal.ofReal ζ) atTop (𝓝 0) := by
    simpa using ENNReal.Tendsto.div_const hb' (Or.inr hε0)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup
    (Eventually.of_forall fun n => bot_le) ?_
  filter_upwards [hZ, hle] with n hZn hn
  calc P n {y | ENNReal.ofReal ζ < Z n y} ≤ P n {y | ENNReal.ofReal ζ ≤ Z n y} :=
        measure_mono fun y (hy : ENNReal.ofReal ζ < Z n y) => le_of_lt hy
    _ ≤ (∫⁻ y, Z n y ∂(P n)) / ENNReal.ofReal ζ :=
        meas_ge_le_lintegral_div hZn.aemeasurable hε0 hεtop
    _ ≤ ENNReal.ofReal (b n) / ENNReal.ofReal ζ := by gcongr

lemma tendsto_const_mul_exp_neg {εt : ℕ → ℝ}
    (h : Tendsto (fun n : ℕ => (n : ℝ) * εt n ^ 2) atTop atTop) (C : ℝ) :
    Tendsto (fun n : ℕ => C * Real.exp (-(n * εt n ^ 2))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun n : ℕ => Real.exp (-(n * εt n ^ 2))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp h
  simpa using h1.const_mul C

/-- **Theorem 1.** -/
theorem asymptotic_theorem : AsymptoticStatement := by
  intro J X f₀ σ pdf εt δ E M a K η μ c4 c5 h
  have hev := eventually_masterHyp h
  have hconc : ∀ᶠ n in atTop,
      MasterConclusion n (J n) σ (X n) (f₀ n) (pdf n) (εt n) (δ n) (M n) (a n) K η μ c4 c5 :=
    hev.mono fun n hn =>
      master_theorem n (J n) σ (X n) (f₀ n) (pdf n) (εt n) (δ n) (E n) (M n) (a n) K η μ c4 c5 hn
  refine ⟨hconc, ?_, ?_⟩
  · intro ζ hζ
    exact tendsto_measure_gt_of_lintegral_le
      (Z := fun n y => posterior σ (X n) (f₀ n) (prior (J n) (pdf n)) y
        (farSet (X n) (f₀ n) (M n * epsRate n (J n) (a n) (εt n))))
      (P := fun n => dataLaw σ (f₀ n))
      (hev.mono fun n hn => by
        have := isProbabilityMeasure_prior hn.hpdf (J n)
        exact measurable_posterior_apply hn.hσ (X n) (f₀ n) _ (measurableSet_farSet _ _ _))
      (tendsto_const_mul_exp_neg h.hnεt 5) (hconc.mono fun n hn => hn.1) hζ
  · intro ζ hζ
    exact tendsto_measure_gt_of_lintegral_le
      (Z := fun n y => posterior σ (X n) (f₀ n) (prior (J n) (pdf n)) y
        (denseSet (δ n) (Aconst K η σ μ c4 c5 * sRate n (J n) (a n) (εt n))))
      (P := fun n => dataLaw σ (f₀ n))
      (hev.mono fun n hn => by
        have := isProbabilityMeasure_prior hn.hpdf (J n)
        exact measurable_posterior_apply hn.hσ (X n) (f₀ n) _ (measurableSet_denseSet _ _))
      (tendsto_const_mul_exp_neg h.hnεt 2) (hconc.mono fun n hn => hn.2) hζ

end LargePrior
