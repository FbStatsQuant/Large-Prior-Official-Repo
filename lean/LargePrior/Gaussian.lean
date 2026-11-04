import LargePrior.Basic

/-!
# Gaussian facts (blueprint Facts 4.5, 7.4, 7.5 and Lemma 7.6)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

variable {n J : ℕ}

instance isProbabilityMeasure_dataLaw (σ : ℝ) (v : Fin n → ℝ) :
    IsProbabilityMeasure (dataLaw σ v) := by
  unfold dataLaw; infer_instance

/-! ### Sub-Gaussian helpers -/

/-- A centred Gaussian random variable with variance `c` has sub-Gaussian mgf with constant `c`. -/
private lemma hasSubgaussianMGF_of_hasLaw {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {X : Ω → ℝ} {c : ℝ≥0} (h : HasLaw X (gaussianReal 0 c) P) : HasSubgaussianMGF X c P := by
  rw [← HasSubgaussianMGF.id_map_iff h.aemeasurable, h.map_eq]
  refine ⟨fun t => ?_, fun t => ?_⟩
  · simpa using (integrable_exp_mul_gaussianReal (μ := 0) (v := c) t)
  · simp [mgf_id_gaussianReal]

/-- Law of one summand of the linear statistic under `dataLaw σ v`. -/
private lemma hasLaw_coord (σ : ℝ) (v w : Fin n → ℝ) (i : Fin n) :
    HasLaw (fun y : Fin n → ℝ => (y i - v i) * w i)
      (gaussianReal 0 (NNReal.mk (w i ^ 2) (sq_nonneg _) * (σ ^ 2).toNNReal)) (dataLaw σ v) := by
  have h0 : HasLaw (fun y : Fin n → ℝ => y i) (gaussianReal (v i) (σ ^ 2).toNNReal)
      (dataLaw σ v) :=
    ⟨(measurable_pi_apply i).aemeasurable,
      (measurePreserving_eval (fun i => gaussianReal (v i) (σ ^ 2).toNNReal) i).map_eq⟩
  have h1 := gaussianReal_mul_const (gaussianReal_sub_const h0 (v i)) (w i)
  simpa using h1

/-- Chernoff bound for the linear statistic, real-valued measure. -/
private lemma measureReal_lin_ge_le (σ : ℝ) (v w : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    (dataLaw σ v).real {y | t ≤ ∑ i, (y i - v i) * w i} ≤
      Real.exp (-(t ^ 2) / (2 * σ ^ 2 * ∑ i, w i ^ 2)) := by
  have hind : iIndepFun (fun i (y : Fin n → ℝ) => (y i - v i) * w i) (dataLaw σ v) :=
    iIndepFun_pi (X := fun i (x : ℝ) => (x - v i) * w i) (fun i => by fun_prop)
  have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hind
    (s := Finset.univ) (fun i _ => hasSubgaussianMGF_of_hasLaw (hasLaw_coord σ v w i)) ht
  convert h using 3
  rw [mul_assoc]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Real.coe_toNNReal _ (sq_nonneg σ)]
  ring

/-- Chernoff bound for a linear statistic of Gaussian data, upper tail (blueprint Fact 7.4). -/
lemma gauss_lin_upper {σ : ℝ} (hσ : 0 < σ) (v w : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    dataLaw σ v {y | t ≤ ∑ i, (y i - v i) * w i} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * σ ^ 2 * ∑ i, w i ^ 2))) := by
  -- `hσ` is part of the frozen statement; the bound holds for every `σ`.
  have _ := hσ
  rw [← ofReal_measureReal]
  exact ENNReal.ofReal_le_ofReal (measureReal_lin_ge_le σ v w ht)

/-- Chernoff bound for a linear statistic of Gaussian data, lower tail (blueprint Fact 7.4). -/
lemma gauss_lin_lower {σ : ℝ} (hσ : 0 < σ) (v w : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) :
    dataLaw σ v {y | ∑ i, (y i - v i) * w i ≤ -t} ≤
      ENNReal.ofReal (Real.exp (-(t ^ 2) / (2 * σ ^ 2 * ∑ i, w i ^ 2))) := by
  have hset : {y : Fin n → ℝ | ∑ i, (y i - v i) * w i ≤ -t} =
      {y | t ≤ ∑ i, (y i - v i) * (-w) i} := by
    ext y
    simp only [Set.mem_ofPred_eq, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib]
    constructor <;> intro h <;> linarith
  have hw : ∑ i, (-w) i ^ 2 = ∑ i, w i ^ 2 := by simp
  rw [hset, ← hw]
  exact gauss_lin_upper hσ v (-w) ht

/-- Two-sided tail of a centred real Gaussian (blueprint Fact 4.5). -/
lemma gaussianReal_abs_gt_le {v : ℝ≥0} (hv : v ≠ 0) {u : ℝ} (hu : 0 ≤ u) :
    gaussianReal 0 v {t | u < |t|} ≤ ENNReal.ofReal (2 * Real.exp (-(u ^ 2) / (2 * v))) := by
  -- `hv` is part of the frozen statement; the bound also holds for `v = 0`.
  have _ := hv
  have hX : HasSubgaussianMGF id v (gaussianReal 0 v) :=
    hasSubgaussianMGF_of_hasLaw ⟨aemeasurable_id, Measure.map_id⟩
  have h1 := hX.measure_ge_le hu
  have h2 := hX.neg.measure_ge_le hu
  have hsub : {t : ℝ | u < |t|} ⊆ {t | u ≤ id t} ∪ {t | u ≤ (-id : ℝ → ℝ) t} := by
    intro t ht
    simp only [Set.mem_ofPred_eq, id, Pi.neg_apply, Set.mem_union] at ht ⊢
    rcases le_or_gt 0 t with h | h
    · left; rw [abs_of_nonneg h] at ht; exact ht.le
    · right; rw [abs_of_neg h] at ht; exact ht.le
  calc gaussianReal 0 v {t | u < |t|}
      ≤ gaussianReal 0 v ({t | u ≤ id t} ∪ {t | u ≤ (-id : ℝ → ℝ) t}) := measure_mono hsub
    _ ≤ gaussianReal 0 v {t | u ≤ id t} + gaussianReal 0 v {t | u ≤ (-id : ℝ → ℝ) t} :=
        measure_union_le _ _
    _ = ENNReal.ofReal ((gaussianReal 0 v).real {t | u ≤ id t}) +
        ENNReal.ofReal ((gaussianReal 0 v).real {t | u ≤ (-id : ℝ → ℝ) t}) := by
        rw [ofReal_measureReal, ofReal_measureReal]
    _ ≤ ENNReal.ofReal (Real.exp (-(u ^ 2) / (2 * v))) +
        ENNReal.ofReal (Real.exp (-(u ^ 2) / (2 * v))) :=
        add_le_add (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    _ = ENNReal.ofReal (2 * Real.exp (-(u ^ 2) / (2 * v))) := by
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le]
        congr 1
        ring

lemma likRatio_pos (σ : ℝ) (f₀ g y : Fin n → ℝ) : 0 < likRatio σ f₀ g y := Real.exp_pos _

/-- `L(g; y) ≤ exp(|y − f₀|² / (2σ²))` (blueprint Remark 2.6). -/
lemma likRatio_le {σ : ℝ} (hσ : 0 < σ) (f₀ g y : Fin n → ℝ) :
    likRatio σ f₀ g y ≤ Real.exp ((∑ i, (y i - f₀ i) ^ 2) / (2 * σ ^ 2)) := by
  unfold likRatio
  apply Real.exp_le_exp.mpr
  have hs : 0 < σ ^ 2 := by positivity
  have hsq : 0 ≤ ∑ i, (y i - g i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hexp : ∑ i, (y i - g i) ^ 2 = ∑ i, (y i - f₀ i) ^ 2
      - 2 * ∑ i, (y i - f₀ i) * (g i - f₀ i) + ∑ i, (g i - f₀ i) ^ 2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hlhs : (∑ i, (y i - f₀ i) * (g i - f₀ i)) / σ ^ 2 - (∑ i, (g i - f₀ i) ^ 2) / (2 * σ ^ 2)
      = (2 * ∑ i, (y i - f₀ i) * (g i - f₀ i) - ∑ i, (g i - f₀ i) ^ 2) / (2 * σ ^ 2) := by
    field_simp
  rw [hlhs]
  apply div_le_div_of_nonneg_right _ (by positivity)
  linarith

lemma continuous_likRatio (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) :
    Continuous (fun p : (Fin J → ℝ) × (Fin n → ℝ) => likRatio σ f₀ (X *ᵥ p.1) p.2) := by
  unfold likRatio
  have hX : Continuous (fun p : (Fin J → ℝ) × (Fin n → ℝ) => X *ᵥ p.1) :=
    continuous_const.matrix_mulVec continuous_fst
  have hXi : ∀ i, Continuous (fun p : (Fin J → ℝ) × (Fin n → ℝ) => (X *ᵥ p.1) i) :=
    fun i => (continuous_apply i).comp hX
  fun_prop

/-! ### Change of measure -/

/-- Tonelli for a product of one-coordinate functions on `Fin n → E`
(adapted from `Theo89/Decomp.lean`). -/
private theorem lintegral_fin_prod {n : ℕ} {E : Type*}
    [MeasurableSpace E] {μ : Fin n → Measure E} [∀ i, SigmaFinite (μ i)]
    (f : Fin n → E → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    ∫⁻ x : Fin n → E, ∏ i, f i (x i) ∂(Measure.pi μ) = ∏ i, ∫⁻ x, f i x ∂(μ i) := by
  induction n with
  | zero => simp
  | succ n n_ih =>
      calc
        _ = ∫⁻ x : E × (Fin n → E),
            f 0 x.1 * ∏ i : Fin n, f (Fin.succ i) (x.2 i)
            ∂((μ 0).prod (Measure.pi (fun i ↦ μ i.succ))) := by
          rw [← ((measurePreserving_piFinSuccAbove μ 0).symm).lintegral_comp_emb
            (MeasurableEquiv.measurableEmbedding _)]
          simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
            Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
            Fin.zero_succAbove, cast_eq, Fin.cons_zero]
        _ = (∫⁻ x, f 0 x ∂μ 0)
            * ∏ i : Fin n, ∫⁻ x, f (Fin.succ i) x ∂(μ i.succ) := by
          rw [← n_ih (fun i => f i.succ) (fun i => hf i.succ), ← lintegral_prod_mul]
          · exact (hf 0).aemeasurable
          · exact (Finset.measurable_prod _ fun i _ =>
              (hf i.succ).comp (measurable_pi_apply i)).aemeasurable
        _ = ∏ i, ∫⁻ x, f i x ∂(μ i) := by rw [Fin.prod_univ_succ]

/-- Product of densities over a common base measure (adapted from `Theo89/Decomp.lean`). -/
private theorem pi_withDensity_fin {E : Type*} [MeasurableSpace E] (μ : Measure E)
    [SigmaFinite μ] (q : Fin n → E → ℝ≥0∞) (hq : ∀ i, Measurable (q i))
    [∀ i, SigmaFinite (μ.withDensity (q i))] :
    Measure.pi (fun i => μ.withDensity (q i)) =
      (Measure.pi fun _ : Fin n => μ).withDensity (fun x => ∏ i, q i (x i)) := by
  refine Measure.pi_eq fun s hs => ?_
  rw [withDensity_apply _ (MeasurableSet.univ_pi hs), Measure.restrict_pi_pi,
    lintegral_fin_prod q hq]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [withDensity_apply _ (hs i)]

/-- `dataLaw σ v` as a density with respect to Lebesgue measure on `Fin n → ℝ`. -/
private lemma dataLaw_eq_withDensity_volume {σ : ℝ} (hσ : 0 < σ) (v : Fin n → ℝ) :
    dataLaw σ v = (Measure.pi fun _ : Fin n => (volume : Measure ℝ)).withDensity
      (fun y => ∏ i, gaussianPDF (v i) (σ ^ 2).toNNReal (y i)) := by
  have hs : (σ ^ 2).toNNReal ≠ 0 := by
    rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity
  have : ∀ i, SigmaFinite ((volume : Measure ℝ).withDensity
      (gaussianPDF (v i) (σ ^ 2).toNNReal)) := fun i => by
    rw [← gaussianReal_of_var_ne_zero _ hs]; infer_instance
  unfold dataLaw
  simp_rw [gaussianReal_of_var_ne_zero _ hs]
  exact pi_withDensity_fin volume _ (fun i => measurable_gaussianPDF _ _)

private lemma measurable_likRatio (σ : ℝ) (f₀ g : Fin n → ℝ) :
    Measurable (fun y => ENNReal.ofReal (likRatio σ f₀ g y)) := by
  have : Continuous (fun y : Fin n → ℝ => likRatio σ f₀ g y) := by
    unfold likRatio; fun_prop
  exact this.measurable.ennreal_ofReal

/-- Pointwise identity `∏ φ(yᵢ; gᵢ) = ∏ φ(yᵢ; f₀ᵢ) · L(g; y)`. -/
private lemma prod_gaussianPDF_eq {σ : ℝ} (hσ : 0 < σ) (f₀ g y : Fin n → ℝ) :
    ∏ i, gaussianPDF (g i) (σ ^ 2).toNNReal (y i) =
      (∏ i, gaussianPDF (f₀ i) (σ ^ 2).toNNReal (y i)) * ENNReal.ofReal (likRatio σ f₀ g y) := by
  simp only [gaussianPDF]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_prod_of_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _),
    ← ENNReal.ofReal_mul (Finset.prod_nonneg fun i _ => gaussianPDFReal_nonneg _ _ _)]
  congr 1
  simp only [gaussianPDFReal, Real.coe_toNNReal _ (sq_nonneg σ), likRatio,
    Finset.prod_mul_distrib, ← Real.exp_sum]
  rw [mul_assoc _ (Real.exp _), ← Real.exp_add]
  congr 2
  have hs : σ ^ 2 ≠ 0 := by positivity
  rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-- Change of measure: `P_g = P_{f₀}` with density `L(g; ·)` (blueprint Fact 7.5). -/
lemma dataLaw_eq_withDensity {σ : ℝ} (hσ : 0 < σ) (f₀ g : Fin n → ℝ) :
    dataLaw σ g = (dataLaw σ f₀).withDensity (fun y => ENNReal.ofReal (likRatio σ f₀ g y)) := by
  have hm : Measurable (fun y : Fin n → ℝ => ∏ i, gaussianPDF (f₀ i) (σ ^ 2).toNNReal (y i)) :=
    Finset.measurable_prod _ fun i _ => (measurable_gaussianPDF _ _).comp (measurable_pi_apply i)
  rw [dataLaw_eq_withDensity_volume hσ g, dataLaw_eq_withDensity_volume hσ f₀,
    ← withDensity_mul _ hm (measurable_likRatio σ f₀ g)]
  congr 1
  funext y
  exact prod_gaussianPDF_eq hσ f₀ g y

lemma lintegral_likRatio_mul {σ : ℝ} (hσ : 0 < σ) (f₀ g : Fin n → ℝ)
    {h : (Fin n → ℝ) → ℝ≥0∞} (hh : Measurable h) :
    ∫⁻ y, ENNReal.ofReal (likRatio σ f₀ g y) * h y ∂(dataLaw σ f₀) = ∫⁻ y, h y ∂(dataLaw σ g) := by
  rw [dataLaw_eq_withDensity hσ f₀ g,
    lintegral_withDensity_eq_lintegral_mul _ (measurable_likRatio σ f₀ g) hh]
  rfl


end LargePrior
