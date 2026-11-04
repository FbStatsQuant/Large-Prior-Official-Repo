import LargePrior.LocalMass

/-!
# Lemma 2: evidence lower bound (blueprint `lem:evidence`)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

variable {n J : ℕ}

/-! ### (i) The ball `B` and bounds on it -/

/-- `B(r)` is closed, hence measurable. Kept as an alias of `measurableSet_localBall` (the frozen
statement list of v2/v3 contains this name); it no longer duplicates the proof. -/
private lemma measurableSet_localBall' (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (r : ℝ) :
    MeasurableSet (localBall X f₀ r) :=
  measurableSet_localBall X f₀ r

private lemma continuous_coord (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (i : Fin n) :
    Continuous fun θ : Fin J → ℝ => (X *ᵥ θ) i - f₀ i :=
  ((continuous_apply i).comp (continuous_const.matrix_mulVec continuous_id)).sub continuous_const

private lemma sum_sq_le_of_mem (hn : 0 < n) {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ}
    {r : ℝ} {θ : Fin J → ℝ} (hθ : θ ∈ localBall X f₀ r) :
    ∑ i, ((X *ᵥ θ) i - f₀ i) ^ 2 ≤ n * r ^ 2 := by
  have h0 := empNorm_nonneg (X *ᵥ θ - f₀)
  have h := sum_sq_eq_mul_empNorm_sq hn (X *ᵥ θ - f₀)
  simp only [Pi.sub_apply] at h
  rw [h]
  have : empNorm (X *ᵥ θ - f₀) ^ 2 ≤ r ^ 2 := pow_le_pow_left₀ h0 hθ 2
  exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)

private lemma abs_le_of_mem {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ} {r : ℝ}
    {θ : Fin J → ℝ} (hθ : θ ∈ localBall X f₀ r) (i : Fin n) :
    |(X *ᵥ θ) i - f₀ i| ≤ Real.sqrt n * r := by
  have h := abs_le_sqrt_mul_empNorm (X *ᵥ θ - f₀) i
  simp only [Pi.sub_apply] at h
  exact h.trans (mul_le_mul_of_nonneg_left hθ (Real.sqrt_nonneg _))

/-! ### (ii) Integrability under a probability measure carried by `B` -/

section integrability

variable {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ} {r : ℝ}
  {ν : Measure (Fin J → ℝ)} [IsProbabilityMeasure ν]

private lemma integrable_coord (hν : ∀ᵐ θ ∂ν, θ ∈ localBall X f₀ r) (i : Fin n) :
    Integrable (fun θ => (X *ᵥ θ) i - f₀ i) ν :=
  Integrable.of_bound (continuous_coord X f₀ i).aestronglyMeasurable (Real.sqrt n * r)
    (hν.mono fun _ hθ => by rw [Real.norm_eq_abs]; exact abs_le_of_mem hθ i)

private lemma integrable_coord_sq (hn : 0 < n) (hν : ∀ᵐ θ ∂ν, θ ∈ localBall X f₀ r)
    (i : Fin n) : Integrable (fun θ => ((X *ᵥ θ) i - f₀ i) ^ 2) ν :=
  Integrable.of_bound ((continuous_coord X f₀ i).pow 2).aestronglyMeasurable (n * r ^ 2)
    (hν.mono fun θ hθ => by
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact le_trans (Finset.single_le_sum (f := fun j => ((X *ᵥ θ) j - f₀ j) ^ 2)
        (fun j _ => sq_nonneg _) (Finset.mem_univ i)) (sum_sq_le_of_mem hn hθ))

private lemma integrable_sumsq (hn : 0 < n) (hν : ∀ᵐ θ ∂ν, θ ∈ localBall X f₀ r) :
    Integrable (fun θ => ∑ i, ((X *ᵥ θ) i - f₀ i) ^ 2) ν :=
  integrable_finsetSum _ fun i _ => integrable_coord_sq hn hν i

end integrability

/-! ### (iii) Jensen lower bound for the evidence -/

/-- The log-likelihood ratio `ℓ_y(θ)`. -/
private def llr (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ y : Fin n → ℝ) (θ : Fin J → ℝ) : ℝ :=
  (∑ i, (y i - f₀ i) * ((X *ᵥ θ) i - f₀ i)) / σ ^ 2 -
    (∑ i, ((X *ᵥ θ) i - f₀ i) ^ 2) / (2 * σ ^ 2)

private lemma likRatio_eq_exp_llr (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ y : Fin n → ℝ)
    (θ : Fin J → ℝ) : likRatio σ f₀ (X *ᵥ θ) y = Real.exp (llr σ X f₀ y θ) := rfl

/-- Jensen's inequality for `exp` (convex on the closed set `ℝ`), in `ℝ≥0∞` form. -/
private lemma ofReal_exp_integral_le {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {G : α → ℝ} (hG : Integrable G μ) :
    ENNReal.ofReal (Real.exp (∫ a, G a ∂μ)) ≤ ∫⁻ a, ENNReal.ofReal (Real.exp (G a)) ∂μ := by
  by_cases h : ∫⁻ a, ENNReal.ofReal (Real.exp (G a)) ∂μ = ∞
  · rw [h]; exact le_top
  have hmeas : AEStronglyMeasurable (fun a => Real.exp (G a)) μ :=
    Real.continuous_exp.comp_aestronglyMeasurable hG.1
  have hpos : (0 : α → ℝ) ≤ᵐ[μ] fun a => Real.exp (G a) :=
    ae_of_all _ fun a => (Real.exp_pos _).le
  have hint : Integrable (fun a => Real.exp (G a)) μ := by
    refine ⟨hmeas, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hpos]
    exact lt_top_iff_ne_top.2 h
  have hJ := convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hG hint
  rw [← ofReal_integral_eq_lintegral_ofReal hint hpos]
  exact ENNReal.ofReal_le_ofReal hJ

/-- `D(y) ≥ Π(B) · exp(∫ ℓ_y dΠ(·|B))`. -/
private lemma evidence_ge_cond (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri] {B : Set (Fin J → ℝ)}
    (hB0 : pri B ≠ 0) (y : Fin n → ℝ) (hint : Integrable (llr σ X f₀ y) pri[|B]) :
    pri B * ENNReal.ofReal (Real.exp (∫ θ, llr σ X f₀ y θ ∂pri[|B])) ≤
      evidence σ X f₀ pri y := by
  have := cond_isProbabilityMeasure (μ := pri) hB0
  calc pri B * ENNReal.ofReal (Real.exp (∫ θ, llr σ X f₀ y θ ∂pri[|B]))
      ≤ pri B * ∫⁻ θ, ENNReal.ofReal (Real.exp (llr σ X f₀ y θ)) ∂pri[|B] :=
        mul_le_mul_right (ofReal_exp_integral_le _ hint) _
    _ = ∫⁻ θ in B, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri := by
        rw [ProbabilityTheory.cond, lintegral_smul_measure, smul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel hB0 (measure_ne_top _ _), one_mul]
        rfl
    _ ≤ evidence σ X f₀ pri y := setLIntegral_le_lintegral _ _

/-! ### (iv) The average of `ℓ_y` and the two quadratic bounds -/

section average

variable {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ} {r : ℝ}
  {ν : Measure (Fin J → ℝ)} [IsProbabilityMeasure ν]

private lemma integrable_llr (hn : 0 < n) (hν : ∀ᵐ θ ∂ν, θ ∈ localBall X f₀ r) (σ : ℝ)
    (y : Fin n → ℝ) : Integrable (llr σ X f₀ y) ν :=
  ((integrable_finsetSum _ fun i _ => (integrable_coord hν i).const_mul (y i - f₀ i)).div_const
    _).sub ((integrable_sumsq hn hν).div_const _)

private lemma integral_llr (hn : 0 < n) (hν : ∀ᵐ θ ∂ν, θ ∈ localBall X f₀ r) (σ : ℝ)
    (y : Fin n → ℝ) :
    ∫ θ, llr σ X f₀ y θ ∂ν =
      (∑ i, (y i - f₀ i) * ∫ θ, ((X *ᵥ θ) i - f₀ i) ∂ν) / σ ^ 2 -
        (∫ θ, ∑ i, ((X *ᵥ θ) i - f₀ i) ^ 2 ∂ν) / (2 * σ ^ 2) := by
  have h1 : Integrable (fun θ => ∑ i, (y i - f₀ i) * ((X *ᵥ θ) i - f₀ i)) ν :=
    integrable_finsetSum _ fun i _ => (integrable_coord hν i).const_mul (y i - f₀ i)
  unfold llr
  rw [integral_sub (h1.div_const _) ((integrable_sumsq hn hν).div_const _), integral_div,
    integral_div, integral_finsetSum _ fun i _ => (integrable_coord hν i).const_mul _]
  simp only [integral_const_mul]

private lemma integral_sumsq_le (hn : 0 < n) (hν : ∀ᵐ θ ∂ν, θ ∈ localBall X f₀ r) :
    ∫ θ, ∑ i, ((X *ᵥ θ) i - f₀ i) ^ 2 ∂ν ≤ n * r ^ 2 := by
  calc ∫ θ, ∑ i, ((X *ᵥ θ) i - f₀ i) ^ 2 ∂ν ≤ ∫ _θ, (n * r ^ 2 : ℝ) ∂ν :=
        integral_mono_ae (integrable_sumsq hn hν) (integrable_const _)
          (hν.mono fun _ hθ => sum_sq_le_of_mem hn hθ)
    _ = n * r ^ 2 := by simp

private lemma sum_sq_integral_le (hn : 0 < n) (hν : ∀ᵐ θ ∂ν, θ ∈ localBall X f₀ r) :
    ∑ i, (∫ θ, ((X *ᵥ θ) i - f₀ i) ∂ν) ^ 2 ≤ n * r ^ 2 := by
  have hJ : ∀ i, (∫ θ, ((X *ᵥ θ) i - f₀ i) ∂ν) ^ 2 ≤ ∫ θ, ((X *ᵥ θ) i - f₀ i) ^ 2 ∂ν :=
    fun i => (Even.convexOn_pow (𝕜 := ℝ) even_two).map_integral_le
      (continuous_pow 2).continuousOn isClosed_univ (ae_of_all _ fun _ => Set.mem_univ _)
      (integrable_coord hν i) (integrable_coord_sq hn hν i)
  calc ∑ i, (∫ θ, ((X *ᵥ θ) i - f₀ i) ∂ν) ^ 2
      ≤ ∑ i, ∫ θ, ((X *ᵥ θ) i - f₀ i) ^ 2 ∂ν := Finset.sum_le_sum fun i _ => hJ i
    _ = ∫ θ, ∑ i, ((X *ᵥ θ) i - f₀ i) ^ 2 ∂ν :=
        (integral_finsetSum _ fun i _ => integrable_coord_sq hn hν i).symm
    _ ≤ n * r ^ 2 := integral_sumsq_le hn hν

end average

/-! ### (v) Gaussian tail -/

private lemma tail_bound {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n) (f₀ : Fin n → ℝ) {L εt : ℝ}
    (hL : 0 < L) (hεt : 0 < εt) (w : Fin n → ℝ) (hw : ∑ i, w i ^ 2 ≤ n * (L * εt) ^ 2) :
    dataLaw σ f₀ {y | ∑ i, (y i - f₀ i) * w i ≤ -(Real.sqrt 2 * σ * L * n * εt ^ 2)} ≤
      ENNReal.ofReal (Real.exp (-(n * εt ^ 2))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < Real.sqrt 2 * σ * L * n * εt ^ 2 := by positivity
  by_cases hQ : ∑ i, w i ^ 2 = 0
  · have hw0 : ∀ i, w i = 0 := fun i => by
      have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => sq_nonneg (w j))).1 hQ i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 this
    have hempty : {y : Fin n → ℝ | ∑ i, (y i - f₀ i) * w i ≤
        -(Real.sqrt 2 * σ * L * n * εt ^ 2)} = ∅ := by
      ext y
      simp only [hw0, mul_zero, Finset.sum_const_zero, Set.mem_ofPred_eq,
        Set.mem_empty_iff_false, iff_false, not_le]
      linarith
    rw [hempty, measure_empty]
    exact zero_le
  · have hQpos : 0 < ∑ i, w i ^ 2 :=
      lt_of_le_of_ne (Finset.sum_nonneg fun i _ => sq_nonneg _) (Ne.symm hQ)
    refine (gauss_lin_lower hσ f₀ w ht.le).trans (ENNReal.ofReal_le_ofReal
      (Real.exp_le_exp.2 ?_))
    rw [neg_div, neg_le_neg_iff, le_div_iff₀ (by positivity)]
    have h2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have key : (Real.sqrt 2 * σ * L * n * εt ^ 2) ^ 2 =
        (n * εt ^ 2 * (2 * σ ^ 2)) * (n * (L * εt) ^ 2) := by
      rw [mul_pow, mul_pow, mul_pow, mul_pow, h2]; ring
    rw [key, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hw (by positivity)

/-! ### (vi) Assembly -/

/-- **Lemma 2** (generic form): if `Π(B(L ε̃)) ≥ exp(−c n ε̃²)` then
`P₀{D < exp(−(c + √2 L/σ + L²/(2σ²)) n ε̃²)} ≤ exp(−n ε̃²)`. -/
theorem evidence_lower {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n) (X : Matrix (Fin n) (Fin J) ℝ)
    (f₀ : Fin n → ℝ) (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri]
    {L εt c : ℝ} (hL : 0 < L) (hεt : 0 < εt) (hc : 0 ≤ c)
    (hmass : ENNReal.ofReal (Real.exp (-(c * n * εt ^ 2))) ≤ pri (localBall X f₀ (L * εt))) :
    dataLaw σ f₀ {y | evidence σ X f₀ pri y <
        ENNReal.ofReal (Real.exp
          (-((c + (Real.sqrt 2 * L / σ + L ^ 2 / (2 * σ ^ 2))) * n * εt ^ 2)))} ≤
      ENNReal.ofReal (Real.exp (-(n * εt ^ 2))) := by
  -- The bound uses the prior-mass inequality directly; `hc` is retained for the frozen interface.
  have _ := hc
  set B := localBall X f₀ (L * εt) with hBdef
  have hBmeas : MeasurableSet B := measurableSet_localBall X f₀ (L * εt)
  have hB0 : pri B ≠ 0 := by
    intro h
    rw [h, nonpos_iff_eq_zero, ENNReal.ofReal_eq_zero] at hmass
    exact absurd hmass (not_le.2 (Real.exp_pos _))
  have := cond_isProbabilityMeasure (μ := pri) hB0
  have hν : ∀ᵐ θ ∂pri[|B], θ ∈ B := ae_cond_mem hBmeas
  set w : Fin n → ℝ := fun i => ∫ θ, ((X *ᵥ θ) i - f₀ i) ∂pri[|B] with hwdef
  have hw : ∑ i, w i ^ 2 ≤ n * (L * εt) ^ 2 := sum_sq_integral_le hn hν
  refine le_trans (measure_mono ?_) (tail_bound hσ hn f₀ hL hεt w hw)
  intro y hy
  simp only [Set.mem_ofPred_eq] at hy ⊢
  by_contra hS
  push Not at hS
  refine absurd hy (not_lt.2 ?_)
  have hI := integral_sumsq_le hn hν
  have hEv := evidence_ge_cond σ X f₀ pri hB0 y (integrable_llr hn hν σ y)
  rw [integral_llr hn hν σ y] at hEv
  refine le_trans ?_ (le_trans (mul_le_mul_left hmass _) hEv)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
  have hσ2 : 0 < σ ^ 2 := by positivity
  have e1 : Real.sqrt 2 * L / σ * n * εt ^ 2 = (Real.sqrt 2 * σ * L * n * εt ^ 2) / σ ^ 2 := by
    field_simp
  have e2 : L ^ 2 / (2 * σ ^ 2) * n * εt ^ 2 = (n * (L * εt) ^ 2) / (2 * σ ^ 2) := by
    field_simp
  have h1 : -(Real.sqrt 2 * σ * L * n * εt ^ 2) / σ ^ 2 ≤
      (∑ i, (y i - f₀ i) * w i) / σ ^ 2 := div_le_div_of_nonneg_right hS.le hσ2.le
  have h2 : (∫ θ, ∑ i, ((X *ᵥ θ) i - f₀ i) ^ 2 ∂pri[|B]) / (2 * σ ^ 2) ≤
      (n * (L * εt) ^ 2) / (2 * σ ^ 2) := div_le_div_of_nonneg_right hI (by positivity)
  rw [neg_div] at h1
  have hg : -((c + (Real.sqrt 2 * L / σ + L ^ 2 / (2 * σ ^ 2))) * n * εt ^ 2) =
      -(c * n * εt ^ 2) - Real.sqrt 2 * L / σ * n * εt ^ 2 - L ^ 2 / (2 * σ ^ 2) * n * εt ^ 2 := by
    ring
  rw [hg, e1, e2]
  linarith

end LargePrior
