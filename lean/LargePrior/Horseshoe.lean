import LargePrior.Posterior

/-!
# The horseshoe density: probability density, tail bound, lower bound (blueprint Part P)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

noncomputable section

namespace LargePrior

/-- `c_HS = e^{−1/2} / (2π √(2π))`, the constant of the lower bound. -/
def hsConst : ℝ := Real.exp (-(1 / 2)) / (2 * Real.pi * Real.sqrt (2 * Real.pi))

/-- Pointwise domination `φ_s(t) ≤ e^{−1/2} / (√(2π) |t|)` (blueprint `lem:phi-dom`). -/
lemma gaussianPDFReal_le_inv_abs {v : ℝ≥0} (hv : v ≠ 0) {t : ℝ} (ht : t ≠ 0) :
    gaussianPDFReal 0 v t ≤ Real.exp (-(1 / 2)) / (Real.sqrt (2 * Real.pi) * |t|) := by
  have hv0 : (0 : ℝ) < v := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hv)
  have hs : 0 < Real.sqrt (v : ℝ) := Real.sqrt_pos.mpr hv0
  have hta : 0 < |t| := abs_pos.mpr ht
  have h2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  set w := |t| / Real.sqrt (v : ℝ) with hw
  have hw0 : 0 ≤ w := by positivity
  have hw2 : w ^ 2 = t ^ 2 / v := by rw [hw, div_pow, sq_abs, Real.sq_sqrt hv0.le]
  have key : w ≤ Real.exp ((w ^ 2 - 1) / 2) := by
    have h1 : w ^ 2 ≤ Real.exp ((w ^ 2 - 1) / 2) ^ 2 := by
      rw [← Real.exp_nat_mul]
      have := Real.add_one_le_exp (w ^ 2 - 1)
      convert this using 2 <;> push_cast <;> ring
    exact (pow_le_pow_iff_left₀ hw0 (Real.exp_pos _).le two_ne_zero).mp h1
  rw [gaussianPDFReal_def]
  simp only [sub_zero]
  rw [Real.sqrt_mul' _ hv0.le, le_div_iff₀ (by positivity)]
  have hrw : (Real.sqrt (2 * Real.pi) * Real.sqrt v)⁻¹ * Real.exp (-t ^ 2 / (2 * v)) *
      (Real.sqrt (2 * Real.pi) * |t|) = w * Real.exp (-(w ^ 2) / 2) := by
    rw [hw2, hw]; field_simp
  rw [hrw]
  calc w * Real.exp (-(w ^ 2) / 2) ≤ Real.exp ((w ^ 2 - 1) / 2) * Real.exp (-(w ^ 2) / 2) :=
        mul_le_mul_of_nonneg_right key (Real.exp_pos _).le
    _ = Real.exp (-(1 / 2)) := by rw [← Real.exp_add]; ring_nf

lemma measurable_halfCauchyPDF : Measurable halfCauchyPDF := by
  unfold halfCauchyPDF
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id) (by fun_prop)
    measurable_const

lemma halfCauchyPDF_nonneg (l : ℝ) : 0 ≤ halfCauchyPDF l := by
  unfold halfCauchyPDF; split_ifs <;> positivity

private lemma halfCauchyPDF_eq_of_pos {l : ℝ} (hl : 0 < l) :
    halfCauchyPDF l = 2 / Real.pi * (1 + l ^ 2)⁻¹ := by
  simp only [halfCauchyPDF, hl, ↓reduceIte]; field_simp

private lemma halfCauchyPDF_le (l : ℝ) : halfCauchyPDF l ≤ 2 / Real.pi * (1 + l ^ 2)⁻¹ := by
  by_cases hl : 0 < l
  · exact (halfCauchyPDF_eq_of_pos hl).le
  · simp only [halfCauchyPDF, hl, ↓reduceIte]; positivity

private lemma integrable_halfCauchyPDF : Integrable halfCauchyPDF := by
  refine Integrable.mono' (integrable_inv_one_add_sq.const_mul (2 / Real.pi))
    measurable_halfCauchyPDF.aestronglyMeasurable (Eventually.of_forall fun l => ?_)
  rw [Real.norm_of_nonneg (halfCauchyPDF_nonneg l)]; exact halfCauchyPDF_le l

/-- `∫₀^∞ f_{C⁺} = 1` (blueprint `lem:halfcauchy`(a)). -/
lemma halfCauchy_lintegral_eq_one :
    ∫⁻ l in Set.Ioi (0 : ℝ), ENNReal.ofReal (halfCauchyPDF l) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal integrable_halfCauchyPDF.integrableOn
    (ae_of_all _ halfCauchyPDF_nonneg)]
  rw [setIntegral_congr_fun measurableSet_Ioi (fun l hl => halfCauchyPDF_eq_of_pos hl)]
  rw [integral_const_mul, integral_Ioi_inv_one_add_sq, Real.arctan_zero, ENNReal.ofReal_eq_one]
  field_simp; ring

/-- `∫_T^∞ f_{C⁺} ≤ 2/(πT)` (blueprint `lem:halfcauchy`(b)). -/
lemma halfCauchy_tail_le {T : ℝ} (hT : 0 < T) :
    ∫⁻ l in Set.Ioi T, ENNReal.ofReal (halfCauchyPDF l) ≤ ENNReal.ofReal (2 / (Real.pi * T)) := by
  have hint : IntegrableOn (fun l : ℝ => 2 / Real.pi * l ^ (-2 : ℝ)) (Set.Ioi T) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hT).const_mul _
  calc ∫⁻ l in Set.Ioi T, ENNReal.ofReal (halfCauchyPDF l)
      ≤ ∫⁻ l in Set.Ioi T, ENNReal.ofReal (2 / Real.pi * l ^ (-2 : ℝ)) := by
        refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioi).mpr
          (ae_of_all _ fun l hl => ?_))
        apply ENNReal.ofReal_le_ofReal
        have hl : 0 < l := hT.trans hl
        rw [halfCauchyPDF_eq_of_pos hl, Real.rpow_neg hl.le, Real.rpow_two]
        gcongr
        linarith
    _ = ENNReal.ofReal (∫ l in Set.Ioi T, 2 / Real.pi * l ^ (-2 : ℝ)) := by
        rw [ofReal_integral_eq_lintegral_ofReal hint]
        exact (ae_restrict_iff' measurableSet_Ioi).mpr
          (ae_of_all _ fun l hl => by have := hT.trans hl; positivity)
    _ = ENNReal.ofReal (2 / (Real.pi * T)) := by
        rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hT]
        congr 1
        norm_num
        rw [Real.rpow_neg_one]
        field_simp

private lemma coe_toNNReal_sq_mul (τ l : ℝ) :
    ((Real.toNNReal (l ^ 2 * τ ^ 2) : ℝ≥0) : ℝ) = l ^ 2 * τ ^ 2 :=
  Real.coe_toNNReal _ (by positivity)

private lemma toNNReal_sq_mul_ne_zero {τ l : ℝ} (hτ : 0 < τ) (hl : 0 < l) :
    Real.toNNReal (l ^ 2 * τ ^ 2) ≠ 0 := by
  rw [Ne, Real.toNNReal_eq_zero, not_le]; positivity

private lemma gpdf_eq (τ l t : ℝ) :
    gaussianPDFReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) t =
      (Real.sqrt (2 * Real.pi * (l ^ 2 * τ ^ 2)))⁻¹ *
        Real.exp (-t ^ 2 / (2 * (l ^ 2 * τ ^ 2))) := by
  rw [gaussianPDFReal_def]; simp only [coe_toNNReal_sq_mul, sub_zero]

private lemma measurable_hsKernel (τ : ℝ) :
    Measurable (fun p : ℝ × ℝ =>
      gaussianPDFReal 0 (Real.toNNReal (p.1 ^ 2 * τ ^ 2)) p.2 * halfCauchyPDF p.1) := by
  simp_rw [gpdf_eq]
  exact Measurable.mul (by fun_prop) (measurable_halfCauchyPDF.comp measurable_fst)

/-- For `t ≠ 0` the horseshoe integrand is integrable on `(0, ∞)` (blueprint
`lem:hs-integrable`). -/
lemma horseshoe_integrand_integrable {τ : ℝ} (hτ : 0 < τ) {t : ℝ} (ht : t ≠ 0) :
    IntegrableOn (fun l => gaussianPDFReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) t * halfCauchyPDF l)
      (Set.Ioi 0) := by
  have hmeas : Measurable
      (fun l => gaussianPDFReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) t * halfCauchyPDF l) :=
    by simp_rw [gpdf_eq]; exact Measurable.mul (by fun_prop) measurable_halfCauchyPDF
  refine Integrable.mono' ((integrable_halfCauchyPDF.const_mul
    (Real.exp (-(1 / 2)) / (Real.sqrt (2 * Real.pi) * |t|))).integrableOn)
    hmeas.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (ae_of_all _ fun l hl => ?_)
  have hl : 0 < l := hl
  rw [Real.norm_of_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (halfCauchyPDF_nonneg l))]
  exact mul_le_mul_of_nonneg_right
    (gaussianPDFReal_le_inv_abs (toNNReal_sq_mul_ne_zero hτ hl) ht) (halfCauchyPDF_nonneg l)

lemma horseshoePDF_nonneg (τ t : ℝ) : 0 ≤ horseshoePDF τ t :=
  integral_nonneg fun l => mul_nonneg (gaussianPDFReal_nonneg _ _ _) (halfCauchyPDF_nonneg l)

private lemma measurable_horseshoePDF (τ : ℝ) : Measurable (horseshoePDF τ) :=
  (((measurable_hsKernel τ).comp measurable_swap).stronglyMeasurable.integral_prod_right'
    (ν := volume.restrict (Set.Ioi (0 : ℝ)))).measurable

private lemma ofReal_horseshoePDF {τ : ℝ} (hτ : 0 < τ) {t : ℝ} (ht : t ≠ 0) :
    ENNReal.ofReal (horseshoePDF τ t) = ∫⁻ l in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) t * halfCauchyPDF l) :=
  ofReal_integral_eq_lintegral_ofReal (horseshoe_integrand_integrable hτ ht)
    (ae_of_all _ fun l => mul_nonneg (gaussianPDFReal_nonneg _ _ _) (halfCauchyPDF_nonneg l))

/-- The Tonelli identity: `∫_S π_τ = ∫₀^∞ f_{C⁺}(λ) N(0, λ²τ²)(S) dλ`. -/
private lemma setLIntegral_horseshoePDF {τ : ℝ} (hτ : 0 < τ) (S : Set ℝ) :
    ∫⁻ t in S, ENNReal.ofReal (horseshoePDF τ t) =
      ∫⁻ l in Set.Ioi (0 : ℝ),
        ENNReal.ofReal (halfCauchyPDF l) * gaussianReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) S := by
  have hae : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
    rw [ae_iff]; simp
  have h1 : ∫⁻ t in S, ENNReal.ofReal (horseshoePDF τ t) = ∫⁻ t in S, ∫⁻ l in Set.Ioi (0 : ℝ),
      ENNReal.ofReal (gaussianPDFReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) t * halfCauchyPDF l) :=
    lintegral_congr_ae (ae_restrict_of_ae (hae.mono fun t ht => ofReal_horseshoePDF hτ ht))
  rw [h1, lintegral_lintegral_swap]
  · refine setLIntegral_congr_fun measurableSet_Ioi (fun l hl => ?_)
    have hl : 0 < l := hl
    rw [gaussianReal_apply 0 (toNNReal_sq_mul_ne_zero hτ hl) S]
    simp_rw [ENNReal.ofReal_mul (gaussianPDFReal_nonneg _ _ _)]
    rw [lintegral_mul_const _ (measurable_gaussianPDFReal _ _).ennreal_ofReal, mul_comm]
    rfl
  · exact (ENNReal.measurable_ofReal.comp
      ((measurable_hsKernel τ).comp measurable_swap)).aemeasurable

/-- **The horseshoe density is a probability density** (blueprint `prop:hs-density`). -/
theorem horseshoe_isProbDensity : HorseshoeDensityStatement := by
  intro τ hτ
  refine ⟨measurable_horseshoePDF τ, horseshoePDF_nonneg τ, ?_⟩
  rw [← setLIntegral_univ, setLIntegral_horseshoePDF hτ Set.univ]
  simp only [measure_univ, mul_one]
  exact halfCauchy_lintegral_eq_one

private lemma gauss_tail_small {τ δ T l : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hl : l ∈ Set.Ioc 0 T) :
    gaussianReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) {t | δ < |t|} ≤
      ENNReal.ofReal (2 * Real.exp (-(δ ^ 2 / (2 * T ^ 2 * τ ^ 2)))) := by
  obtain ⟨hl0, hlT⟩ := hl
  refine (gaussianReal_abs_gt_le (toNNReal_sq_mul_ne_zero hτ hl0) hδ.le).trans
    (ENNReal.ofReal_le_ofReal ?_)
  rw [coe_toNNReal_sq_mul]
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by norm_num)
  rw [neg_div, neg_le_neg_iff]
  apply div_le_div_of_nonneg_left (by positivity) (by positivity)
  have : l ^ 2 ≤ T ^ 2 := pow_le_pow_left₀ hl0.le hlT 2
  nlinarith [sq_nonneg τ]

/-- **Tail bound** (blueprint `prop:hs-tail`). -/
theorem horseshoe_tail {τ δ T : ℝ} (hτ : 0 < τ) (hδ : 0 < δ) (hT : 0 < T) :
    coordPrior (horseshoePDF τ) {t | δ < |t|} ≤
      ENNReal.ofReal (2 * Real.exp (-(δ ^ 2 / (2 * T ^ 2 * τ ^ 2))) + 2 / (Real.pi * T)) := by
  have hS : MeasurableSet {t : ℝ | δ < |t|} := measurableSet_lt measurable_const measurable_abs
  rw [coordPrior, withDensity_apply _ hS, setLIntegral_horseshoePDF hτ,
    ← Set.Ioc_union_Ioi_eq_Ioi hT.le]
  refine (lintegral_union_le _ _ _).trans ?_
  rw [ENNReal.ofReal_add (by positivity) (by positivity)]
  set A := ENNReal.ofReal (2 * Real.exp (-(δ ^ 2 / (2 * T ^ 2 * τ ^ 2))))
  gcongr ?_ + ?_
  · calc _ ≤ ∫⁻ l in Set.Ioc 0 T, ENNReal.ofReal (halfCauchyPDF l) * A := by
          refine lintegral_mono_ae ((ae_restrict_iff' measurableSet_Ioc).mpr
            (ae_of_all _ fun l hl => ?_))
          gcongr
          exact gauss_tail_small hτ hδ hl
      _ = (∫⁻ l in Set.Ioc 0 T, ENNReal.ofReal (halfCauchyPDF l)) * A :=
          lintegral_mul_const _ (ENNReal.measurable_ofReal.comp measurable_halfCauchyPDF)
      _ ≤ 1 * A := by
          gcongr
          rw [← halfCauchy_lintegral_eq_one]
          exact lintegral_mono_set Set.Ioc_subset_Ioi_self
      _ = A := one_mul A
  · calc _ ≤ ∫⁻ l in Set.Ioi T, ENNReal.ofReal (halfCauchyPDF l) := by
          refine lintegral_mono fun l => ?_
          calc _ ≤ ENNReal.ofReal (halfCauchyPDF l) * 1 := by gcongr; exact prob_le_one
            _ = _ := mul_one _
      _ ≤ _ := halfCauchy_tail_le hT

/-- **Tail at a polynomial level** (blueprint `cor:hs-tail-J`). -/
theorem horseshoe_tail_le_J {τ u μ : ℝ} {J : ℕ} (hτ : 0 < τ) (hu : 0 < u) (hJ : 2 ≤ J)
    (hμ : 0 < μ)
    (hτu : τ ≤ Real.pi / 4 * (u * (J : ℝ) ^ (-(1 + μ))) /
      Real.sqrt (2 * ((1 + μ) * Real.log J + Real.log 4))) :
    coordPrior (horseshoePDF τ) {t | u < |t|} ≤ ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ))) := by
  have hJ1 : (1 : ℝ) < J := by exact_mod_cast (by omega : 1 < J)
  have hJ0 : (0 : ℝ) < J := by linarith
  have hlogJ : 0 < Real.log J := Real.log_pos hJ1
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  set p := (J : ℝ) ^ (-(1 + μ)) with hp
  have hp0 : 0 < p := Real.rpow_pos_of_pos hJ0 _
  set Λ := (1 + μ) * Real.log J + Real.log 4 with hΛ
  have hΛ0 : 0 < Λ := by positivity
  have hexpΛ : Real.exp (-Λ) = p / 4 := by
    have : -Λ = Real.log J * (-(1 + μ)) + -Real.log 4 := by rw [hΛ]; ring
    rw [this, Real.exp_add, Real.exp_neg, Real.exp_log (by norm_num), hp,
      Real.rpow_def_of_pos hJ0]
    ring
  set T := 4 / (Real.pi * p) with hT
  have hT0 : 0 < T := by positivity
  have hsq : 0 < Real.sqrt (2 * Λ) := Real.sqrt_pos.mpr (by positivity)
  have hTτ : T * τ ≤ u / Real.sqrt (2 * Λ) := by
    calc T * τ ≤ T * (Real.pi / 4 * (u * p) / Real.sqrt (2 * Λ)) :=
          mul_le_mul_of_nonneg_left hτu hT0.le
      _ = u / Real.sqrt (2 * Λ) := by rw [hT]; field_simp
  have hΛle : Λ ≤ u ^ 2 / (2 * T ^ 2 * τ ^ 2) := by
    have h1 : (T * τ) ^ 2 ≤ (u / Real.sqrt (2 * Λ)) ^ 2 := pow_le_pow_left₀ (by positivity) hTτ 2
    rw [div_pow, Real.sq_sqrt (by positivity), le_div_iff₀ (by positivity)] at h1
    rw [le_div_iff₀ (by positivity)]
    nlinarith
  refine (horseshoe_tail hτ hu hT0).trans (ENNReal.ofReal_le_ofReal ?_)
  have h2 : 2 / (Real.pi * T) = p / 2 := by rw [hT]; field_simp; norm_num
  have h3 : Real.exp (-(u ^ 2 / (2 * T ^ 2 * τ ^ 2))) ≤ p / 4 := by
    rw [← hexpΛ]; exact Real.exp_le_exp.mpr (neg_le_neg hΛle)
  linarith

lemma hsConst_ge : 1 / 32 ≤ hsConst := by
  have he : Real.exp (1 / 2) ≤ 2 := by
    have h1 : Real.exp (1 / 2) ^ 2 = Real.exp 1 := by rw [← Real.exp_nat_mul]; norm_num
    have h2 : Real.exp 1 < 4 := Real.exp_one_lt_d9.trans (by norm_num)
    nlinarith [Real.exp_pos (1 / 2)]
  have he' : 1 / 2 ≤ Real.exp (-(1 / 2)) := by
    have := inv_anti₀ (Real.exp_pos (1 / 2)) he
    rw [Real.exp_neg]; linarith [show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
  have hπ : Real.pi < 3.15 := Real.pi_lt_d2
  have hs : Real.sqrt (2 * Real.pi) ≤ 2.52 := by
    calc Real.sqrt (2 * Real.pi) ≤ Real.sqrt (2.52 ^ 2) := Real.sqrt_le_sqrt (by nlinarith)
      _ = 2.52 := Real.sqrt_sq (by norm_num)
  have hden : 2 * Real.pi * Real.sqrt (2 * Real.pi) ≤ 16 := by
    have := Real.sqrt_nonneg (2 * Real.pi); nlinarith [Real.pi_pos]
  unfold hsConst
  rw [le_div_iff₀ (by positivity)]
  nlinarith

private lemma hs_lower_pointwise {τ t m l : ℝ} (hτ : 0 < τ) (hm : |t| ≤ m) (hl1 : 1 ≤ l)
    (hlm : m ≤ l * τ) :
    Real.exp (-(1 / 2)) / (Real.pi * Real.sqrt (2 * Real.pi) * τ) * l ^ (-3 : ℝ) ≤
      gaussianPDFReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) t * halfCauchyPDF l := by
  have hl : 0 < l := by linarith
  rw [gpdf_eq, halfCauchyPDF_eq_of_pos hl]
  have hsq : Real.sqrt (2 * Real.pi * (l ^ 2 * τ ^ 2)) = Real.sqrt (2 * Real.pi) * (l * τ) := by
    rw [Real.sqrt_mul (by positivity), show l ^ 2 * τ ^ 2 = (l * τ) ^ 2 by ring,
      Real.sqrt_sq (by positivity)]
  rw [hsq]
  have hexp : Real.exp (-(1 / 2)) ≤ Real.exp (-t ^ 2 / (2 * (l ^ 2 * τ ^ 2))) := by
    apply Real.exp_le_exp.mpr
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ (by positivity)]
    have : t ^ 2 ≤ (l * τ) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg t) (hm.trans hlm) 2
    nlinarith
  have hc : (Real.pi * l ^ 2)⁻¹ ≤ 2 / Real.pi * (1 + l ^ 2)⁻¹ := by
    have : 2 / Real.pi * (1 + l ^ 2)⁻¹ = (Real.pi * ((1 + l ^ 2) / 2))⁻¹ := by
      field_simp
    rw [this]
    exact inv_anti₀ (by positivity)
      (mul_le_mul_of_nonneg_left (by nlinarith) Real.pi_pos.le)
  have h2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
  rw [Real.rpow_neg hl.le, show l ^ (3 : ℝ) = l ^ 3 by exact_mod_cast Real.rpow_natCast l 3]
  calc Real.exp (-(1 / 2)) / (Real.pi * Real.sqrt (2 * Real.pi) * τ) * (l ^ 3)⁻¹
      = ((Real.sqrt (2 * Real.pi) * (l * τ))⁻¹ * Real.exp (-(1 / 2))) * (Real.pi * l ^ 2)⁻¹ := by
        field_simp
    _ ≤ ((Real.sqrt (2 * Real.pi) * (l * τ))⁻¹ * Real.exp (-t ^ 2 / (2 * (l ^ 2 * τ ^ 2)))) *
          (2 / Real.pi * (1 + l ^ 2)⁻¹) := by
        gcongr

/-- **Lower bound** (blueprint `prop:hs-lower`). -/
theorem horseshoe_lower {τ E t : ℝ} (hτ : 0 < τ) (hE : 0 < E) (ht0 : t ≠ 0) (htE : |t| ≤ E) :
    hsConst * τ / max E τ ^ 2 ≤ horseshoePDF τ t := by
  set m := max E τ with hm
  have hm0 : 0 < m := lt_of_lt_of_le hE (le_max_left _ _)
  set l0 := m / τ with hl0
  have hl01 : 1 ≤ l0 := by rw [hl0, le_div_iff₀ hτ, one_mul]; exact le_max_right _ _
  have hl00 : 0 < l0 := by linarith
  set c := Real.exp (-(1 / 2)) / (Real.pi * Real.sqrt (2 * Real.pi) * τ) with hc
  have hint := horseshoe_integrand_integrable hτ ht0
  have hpow : IntegrableOn (fun l : ℝ => c * l ^ (-3 : ℝ)) (Set.Ioi l0) :=
    (integrableOn_Ioi_rpow_of_lt (by norm_num) hl00).const_mul c
  calc hsConst * τ / m ^ 2 = ∫ l in Set.Ioi l0, c * l ^ (-3 : ℝ) := by
          rw [integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hl00]
          norm_num
          rw [hc, hl0, hsConst]
          have h2π : 0 < Real.sqrt (2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
          field_simp
    _ ≤ ∫ l in Set.Ioi l0,
          gaussianPDFReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) t * halfCauchyPDF l := by
          refine setIntegral_mono_on hpow (hint.mono_set (Set.Ioi_subset_Ioi hl00.le))
            measurableSet_Ioi (fun l hl => ?_)
          have hl : l0 < l := hl
          exact hs_lower_pointwise hτ (htE.trans (le_max_left _ _)) (by linarith)
            ((div_lt_iff₀ hτ).mp hl).le
    _ ≤ horseshoePDF τ t :=
          setIntegral_mono_set hint
            (ae_of_all _ fun l => mul_nonneg (gaussianPDFReal_nonneg _ _ _)
              (halfCauchyPDF_nonneg l))
            (Set.Ioi_subset_Ioi hl00.le).eventuallyLE

end LargePrior
