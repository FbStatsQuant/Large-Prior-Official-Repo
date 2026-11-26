import LargePrior.Gaussian

/-!
# Posterior facts and the posterior decomposition
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

variable {n J : ℕ}

/-- Joint measurability of `(y, θ) ↦ L(θ; y)`. -/
private lemma measurable_lik_swap (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) :
    Measurable (fun p : (Fin n → ℝ) × (Fin J → ℝ) =>
      ENNReal.ofReal (likRatio σ f₀ (X *ᵥ p.2) p.1)) :=
  ((continuous_likRatio σ X f₀).comp continuous_swap).measurable.ennreal_ofReal

/-- Measurability of `θ ↦ L(θ; y)` for fixed `y`. -/
private lemma measurable_lik_theta (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (y : Fin n → ℝ) :
    Measurable (fun θ : Fin J → ℝ => ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y)) :=
  ((continuous_likRatio σ X f₀).comp
    (continuous_id.prodMk continuous_const)).measurable.ennreal_ofReal

/-- Measurability of `y ↦ ∫ L(θ; y) dν(θ)` for an s-finite `ν`. -/
private lemma measurable_lintegral_lik (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (ν : Measure (Fin J → ℝ)) [SFinite ν] :
    Measurable (fun y => ∫⁻ θ, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂ν) :=
  (measurable_lik_swap σ X f₀).lintegral_prod_right'

lemma isProbabilityMeasure_coordPrior {pdf : ℝ → ℝ} (h : IsProbDensity pdf) :
    IsProbabilityMeasure (coordPrior pdf) := by
  constructor
  rw [coordPrior, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact h.lintegral_eq_one

lemma isProbabilityMeasure_prior {pdf : ℝ → ℝ} (h : IsProbDensity pdf) (J : ℕ) :
    IsProbabilityMeasure (prior J pdf) := by
  have := isProbabilityMeasure_coordPrior h
  unfold prior
  infer_instance

lemma evidence_pos (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri] (y : Fin n → ℝ) :
    0 < evidence σ X f₀ pri y := by
  rw [pos_iff_ne_zero, evidence, Ne, lintegral_eq_zero_iff (measurable_lik_theta σ X f₀ y)]
  intro h
  obtain ⟨θ, hθ⟩ := h.exists
  simp only [Pi.zero_apply, ENNReal.ofReal_eq_zero] at hθ
  exact absurd hθ (not_le.mpr (likRatio_pos σ f₀ _ y))

lemma evidence_ne_top {σ : ℝ} (hσ : 0 < σ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri] (y : Fin n → ℝ) :
    evidence σ X f₀ pri y ≠ ∞ := by
  refine ne_top_of_le_ne_top (b := ∫⁻ _ : Fin J → ℝ,
    ENNReal.ofReal (Real.exp ((∑ i, (y i - f₀ i) ^ 2) / (2 * σ ^ 2))) ∂pri) ?_ ?_
  · rw [lintegral_const, measure_univ, mul_one]
    exact ENNReal.ofReal_ne_top
  · exact lintegral_mono fun θ => ENNReal.ofReal_le_ofReal (likRatio_le hσ f₀ _ y)

lemma isProbabilityMeasure_posterior {σ : ℝ} (hσ : 0 < σ) (X : Matrix (Fin n) (Fin J) ℝ)
    (f₀ : Fin n → ℝ) (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri] (y : Fin n → ℝ) :
    IsProbabilityMeasure (posterior σ X f₀ pri y) := by
  constructor
  rw [posterior, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  exact ENNReal.inv_mul_cancel (evidence_pos σ X f₀ pri y).ne' (evidence_ne_top hσ X f₀ pri y)

lemma posterior_apply (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (pri : Measure (Fin J → ℝ)) (y : Fin n → ℝ) {H : Set (Fin J → ℝ)} (hH : MeasurableSet H) :
    posterior σ X f₀ pri y H =
      (∫⁻ θ in H, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) / evidence σ X f₀ pri y := by
  rw [posterior, Measure.smul_apply, withDensity_apply _ hH, smul_eq_mul, ENNReal.div_eq_inv_mul]

lemma measurable_posterior_apply {σ : ℝ} (hσ : 0 < σ) (X : Matrix (Fin n) (Fin J) ℝ)
    (f₀ : Fin n → ℝ) (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri]
    {H : Set (Fin J → ℝ)} (hH : MeasurableSet H) :
    Measurable (fun y => posterior σ X f₀ pri y H) := by
  -- `hσ` is part of the statement; measurability holds for every `σ`.
  have _ := hσ
  simp_rw [posterior_apply σ X f₀ pri _ hH, ENNReal.div_eq_inv_mul]
  exact (measurable_lintegral_lik σ X f₀ pri).inv.mul
    (measurable_lintegral_lik σ X f₀ (pri.restrict H))

/-- Pointwise form of the decomposition. -/
private lemma posterior_le_pointwise {σ : ℝ} (hσ : 0 < σ) (X : Matrix (Fin n) (Fin J) ℝ)
    (f₀ : Fin n → ℝ) (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri]
    {U Θc : Set (Fin J → ℝ)} {R : Set (Fin n → ℝ)} (hU : MeasurableSet U)
    {dstar : ℝ} (hd : 0 < dstar) (y : Fin n → ℝ) :
    posterior σ X f₀ pri y U ≤
      R.indicator 1 y + {y | evidence σ X f₀ pri y < ENNReal.ofReal dstar}.indicator 1 y +
        ENNReal.ofReal dstar⁻¹ *
          ((∫⁻ θ in Θc, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) +
            Rᶜ.indicator 1 y *
              ∫⁻ θ in U ∩ Θcᶜ, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) := by
  have := isProbabilityMeasure_posterior hσ X f₀ pri y
  by_cases hy : y ∈ R
  · rw [Set.indicator_of_mem hy, add_assoc]
    exact prob_le_one.trans le_self_add
  by_cases hD : evidence σ X f₀ pri y < ENNReal.ofReal dstar
  · rw [Set.indicator_of_mem (show y ∈ {y | evidence σ X f₀ pri y < ENNReal.ofReal dstar} from hD)]
    exact prob_le_one.trans (le_add_right le_add_self)
  rw [not_lt] at hD
  rw [Set.indicator_of_mem (show y ∈ Rᶜ from hy), Pi.one_apply, one_mul,
    posterior_apply σ X f₀ pri y hU]
  refine le_trans ?_ le_add_self
  calc (∫⁻ θ in U, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) / evidence σ X f₀ pri y
      ≤ (∫⁻ θ in U, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) / ENNReal.ofReal dstar :=
        ENNReal.div_le_div_left hD _
    _ ≤ ((∫⁻ θ in Θc, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) +
          ∫⁻ θ in U ∩ Θcᶜ, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) /
            ENNReal.ofReal dstar := by
        gcongr
        refine le_trans (lintegral_mono_set ?_) (lintegral_union_le _ _ _)
        intro θ hθ
        by_cases h : θ ∈ Θc
        · exact Or.inl h
        · exact Or.inr ⟨hθ, h⟩
    _ = _ := by rw [ENNReal.div_eq_inv_mul, ENNReal.ofReal_inv_of_pos hd]

/-- `∫ (∫_S L(θ; y) dΠ(θ)) h(y) dP₀(y) = ∫_S P_{Xθ}(h) dΠ(θ)` (Tonelli plus change of measure). -/
private lemma lintegral_setLIntegral_lik_mul {σ : ℝ} (hσ : 0 < σ)
    (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (pri : Measure (Fin J → ℝ))
    [IsProbabilityMeasure pri] (S : Set (Fin J → ℝ)) {h : (Fin n → ℝ) → ℝ≥0∞}
    (hh : Measurable h) :
    ∫⁻ y, (∫⁻ θ in S, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) * h y ∂(dataLaw σ f₀) =
      ∫⁻ θ in S, ∫⁻ y, h y ∂(dataLaw σ (X *ᵥ θ)) ∂pri := by
  have hjoint : Measurable (fun p : (Fin n → ℝ) × (Fin J → ℝ) =>
      ENNReal.ofReal (likRatio σ f₀ (X *ᵥ p.2) p.1) * h p.1) :=
    (measurable_lik_swap σ X f₀).mul (hh.comp measurable_fst)
  simp_rw [← lintegral_mul_const _ (measurable_lik_theta σ X f₀ _)]
  rw [lintegral_lintegral_swap hjoint.aemeasurable]
  refine lintegral_congr fun θ => ?_
  exact lintegral_likRatio_mul hσ f₀ (X *ᵥ θ) hh

/-- The decomposition of `E₀ Π(U | Y)` (`eq:decomposition`, `eq:remainder`). -/
theorem posterior_decomposition {σ : ℝ} (hσ : 0 < σ) (X : Matrix (Fin n) (Fin J) ℝ)
    (f₀ : Fin n → ℝ) (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri]
    {U Θc : Set (Fin J → ℝ)} {R : Set (Fin n → ℝ)} (hU : MeasurableSet U)
    (hΘc : MeasurableSet Θc) (hR : MeasurableSet R) {dstar : ℝ} (hd : 0 < dstar) :
    ∫⁻ y, posterior σ X f₀ pri y U ∂(dataLaw σ f₀) ≤
      dataLaw σ f₀ R + dataLaw σ f₀ {y | evidence σ X f₀ pri y < ENNReal.ofReal dstar} +
        ENNReal.ofReal dstar⁻¹ *
          (pri Θc + ∫⁻ θ in U ∩ Θcᶜ, dataLaw σ (X *ᵥ θ) Rᶜ ∂pri) := by
  -- `hΘc` is part of the statement; the bound holds for every `Θc`.
  have _ := hΘc
  have hDm : MeasurableSet {y | evidence σ X f₀ pri y < ENNReal.ofReal dstar} :=
    measurableSet_lt (measurable_lintegral_lik σ X f₀ pri) measurable_const
  have hA : Measurable (fun y => ∫⁻ θ in Θc, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) :=
    measurable_lintegral_lik σ X f₀ (pri.restrict Θc)
  have hB : Measurable (fun y => Rᶜ.indicator 1 y *
      ∫⁻ θ in U ∩ Θcᶜ, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) :=
    (measurable_one.indicator hR.compl).mul (measurable_lintegral_lik σ X f₀ _)
  have hA' : ∫⁻ y, (∫⁻ θ in Θc, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri)
      ∂(dataLaw σ f₀) = pri Θc := by
    have := lintegral_setLIntegral_lik_mul hσ X f₀ pri Θc (h := fun _ => 1) measurable_const
    simp only [mul_one, lintegral_const, measure_univ] at this
    rw [this, one_mul, Measure.restrict_apply_univ]
  have hB' : ∫⁻ y, Rᶜ.indicator 1 y *
      ∫⁻ θ in U ∩ Θcᶜ, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri ∂(dataLaw σ f₀) =
      ∫⁻ θ in U ∩ Θcᶜ, dataLaw σ (X *ᵥ θ) Rᶜ ∂pri := by
    simp_rw [mul_comm (Rᶜ.indicator 1 _)]
    rw [lintegral_setLIntegral_lik_mul hσ X f₀ pri _ (measurable_one.indicator hR.compl)]
    exact lintegral_congr fun θ => lintegral_indicator_one hR.compl
  calc ∫⁻ y, posterior σ X f₀ pri y U ∂(dataLaw σ f₀)
      ≤ ∫⁻ y, (R.indicator 1 y +
          {y | evidence σ X f₀ pri y < ENNReal.ofReal dstar}.indicator 1 y +
          ENNReal.ofReal dstar⁻¹ *
            ((∫⁻ θ in Θc, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) +
              Rᶜ.indicator 1 y *
                ∫⁻ θ in U ∩ Θcᶜ, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri))
          ∂(dataLaw σ f₀) :=
        lintegral_mono fun y => posterior_le_pointwise hσ X f₀ pri hU hd y
    _ = _ := by
        have h1 : Measurable (fun y => R.indicator (1 : (Fin n → ℝ) → ℝ≥0∞) y +
            {y | evidence σ X f₀ pri y < ENNReal.ofReal dstar}.indicator 1 y) :=
          (measurable_one.indicator hR).add (measurable_one.indicator hDm)
        have h2 : Measurable (fun y =>
            (∫⁻ θ in Θc, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) +
              Rᶜ.indicator 1 y *
                ∫⁻ θ in U ∩ Θcᶜ, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri) :=
          hA.add hB
        rw [lintegral_add_left h1,
          lintegral_add_left (measurable_one.indicator hR), lintegral_indicator_one hR,
          lintegral_indicator_one hDm, lintegral_const_mul _ h2,
          lintegral_add_left hA, hA', hB']

end LargePrior
