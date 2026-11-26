import LargePrior.Spec

/-!
# Elementary facts: empirical norm, rates, constants
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

variable {n J : ℕ}

/-! ## Empirical norm -/

lemma empNorm_nonneg (u : Fin n → ℝ) : 0 ≤ empNorm u := Real.sqrt_nonneg _

lemma empNorm_zero : empNorm (0 : Fin n → ℝ) = 0 := by
  simp [empNorm]

lemma sum_sq_eq_mul_empNorm_sq (hn : 0 < n) (u : Fin n → ℝ) :
    ∑ i, u i ^ 2 = n * empNorm u ^ 2 := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  rw [empNorm, Real.sq_sqrt (by positivity)]
  field_simp

lemma abs_le_sqrt_mul_empNorm (u : Fin n → ℝ) (i : Fin n) :
    |u i| ≤ Real.sqrt n * empNorm u := by
  have hn : (0 : ℝ) < n := by
    exact_mod_cast (Nat.pos_of_ne_zero (fun h => by subst h; exact i.elim0))
  have h1 : Real.sqrt n * empNorm u = Real.sqrt (∑ i, u i ^ 2) := by
    rw [empNorm, ← Real.sqrt_mul hn.le]
    congr 1
    field_simp
  rw [h1]
  apply Real.abs_le_sqrt
  exact Finset.single_le_sum (f := fun i => u i ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)

private lemma empNorm_eq_norm (u : Fin n → ℝ) :
    empNorm u = ‖(WithLp.toLp 2 u : EuclideanSpace ℝ (Fin n))‖ / Real.sqrt n := by
  rw [empNorm, EuclideanSpace.norm_eq, Real.sqrt_div' _ (Nat.cast_nonneg n)]
  simp

lemma empNorm_add_le (u v : Fin n → ℝ) : empNorm (u + v) ≤ empNorm u + empNorm v := by
  rw [empNorm_eq_norm, empNorm_eq_norm, empNorm_eq_norm, ← add_div]
  gcongr
  exact norm_add_le _ _

lemma empNorm_smul (c : ℝ) (u : Fin n → ℝ) : empNorm (c • u) = |c| * empNorm u := by
  simp only [empNorm, Pi.smul_apply, smul_eq_mul, mul_pow, ← Finset.mul_sum, mul_div_assoc]
  rw [Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

lemma empNorm_neg (u : Fin n → ℝ) : empNorm (-u) = empNorm u := by
  simpa using empNorm_smul (-1) u

lemma empNorm_sub_comm (u v : Fin n → ℝ) : empNorm (u - v) = empNorm (v - u) := by
  rw [← neg_sub, empNorm_neg]

lemma empNorm_sub_le (u v w : Fin n → ℝ) :
    empNorm (u - w) ≤ empNorm (u - v) + empNorm (v - w) := by
  have : u - w = (u - v) + (v - w) := by abel
  rw [this]
  exact empNorm_add_le _ _

lemma continuous_empNorm : Continuous (empNorm : (Fin n → ℝ) → ℝ) := by
  unfold empNorm
  fun_prop

/-- An average of squares never exceeds the largest square. -/
lemma empNorm_le_of_abs_le {b : ℝ} (hb : 0 ≤ b) (u : Fin n → ℝ) (h : ∀ i, |u i| ≤ b) :
    empNorm u ≤ b := by
  rw [empNorm]
  refine Real.sqrt_le_iff.2 ⟨hb, ?_⟩
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero, div_zero]
    positivity
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_le_iff₀ hn']
    calc ∑ i, u i ^ 2 ≤ ∑ _i : Fin n, b ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have := pow_le_pow_left₀ (abs_nonneg (u i)) (h i) 2
            rwa [sq_abs] at this
      _ = b ^ 2 * n := by simp [mul_comm]

/-- Under Assumption 1, `‖Xθ‖_{2,n} ≤ K ‖θ‖₁`. -/
lemma empNorm_mulVec_le {X : Matrix (Fin n) (Fin J) ℝ} {K : ℝ} (hX : BasisBound X K)
    (θ : Fin J → ℝ) : empNorm (X *ᵥ θ) ≤ K * ∑ j, |θ j| := by
  have hsum : ∀ (s : Finset (Fin J)) (f : Fin J → Fin n → ℝ),
      empNorm (∑ j ∈ s, f j) ≤ ∑ j ∈ s, empNorm (f j) := by
    intro s f
    induction s using Finset.induction_on with
    | empty => simp [empNorm_zero]
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (empNorm_add_le _ _).trans (by linarith)
  have hXθ : X *ᵥ θ = ∑ j, θ j • (fun i => X i j) := by
    funext i
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]
  rw [hXθ, Finset.mul_sum]
  refine (hsum _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [empNorm_smul, mul_comm K]
  exact mul_le_mul_of_nonneg_left (hX j) (abs_nonneg _)

/-! ## Rates (`fact:rates`) -/

lemma le_sRate (n J a : ℕ) (εt : ℝ) : a ≤ sRate n J a εt := le_max_left _ _

lemma one_le_sRate {n J a : ℕ} {εt : ℝ} (ha : 1 ≤ a) : 1 ≤ sRate n J a εt :=
  le_trans ha (le_sRate n J a εt)

lemma mul_epsRate_sq (hn : 0 < n) (hJ : 2 ≤ J) (a : ℕ) (εt : ℝ) :
    (n : ℝ) * epsRate n J a εt ^ 2 = sRate n J a εt * Real.log J := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ' : (0 : ℝ) ≤ Real.log J :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ J))
  rw [epsRate, Real.sq_sqrt (by positivity)]
  field_simp

lemma epsRate_ge (hn : 0 < n) (hJ : 2 ≤ J) (a : ℕ) {εt : ℝ} (hεt : 0 ≤ εt) :
    εt ≤ epsRate n J a εt := by
  have _ := hεt -- not needed: `Real.le_sqrt_of_sq_le` holds for all signs
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ' : 0 < Real.log J := Real.log_pos (by exact_mod_cast (by omega : 1 < J))
  rw [epsRate]
  apply Real.le_sqrt_of_sq_le
  rw [le_div_iff₀ hn']
  have h1 : (n : ℝ) * εt ^ 2 / Real.log J ≤ sRate n J a εt :=
    (Nat.le_ceil _).trans (by exact_mod_cast le_max_right _ _)
  rw [div_le_iff₀ hJ'] at h1
  linarith

lemma epsRate_pos (hn : 0 < n) (hJ : 2 ≤ J) {a : ℕ} (ha : 1 ≤ a) (εt : ℝ) :
    0 < epsRate n J a εt := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hJ' : 0 < Real.log J := Real.log_pos (by exact_mod_cast (by omega : 1 < J))
  have hs : (0 : ℝ) < sRate n J a εt := by exact_mod_cast one_le_sRate (εt := εt) ha
  rw [epsRate]
  exact Real.sqrt_pos.2 (by positivity)

lemma log_two_le_mul_epsRate_sq (hn : 0 < n) (hJ : 2 ≤ J) {a : ℕ} (ha : 1 ≤ a) (εt : ℝ) :
    Real.log 2 ≤ n * epsRate n J a εt ^ 2 := by
  have hJ' : 0 < Real.log J := Real.log_pos (by exact_mod_cast (by omega : 1 < J))
  have hs : (1 : ℝ) ≤ sRate n J a εt := by exact_mod_cast one_le_sRate (εt := εt) ha
  have h2 : Real.log 2 ≤ Real.log J := Real.log_le_log (by norm_num) (by exact_mod_cast hJ)
  rw [mul_epsRate_sq hn hJ]
  nlinarith

/-! ## Constants -/

lemma Ltil_pos {K η : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η) : 0 < Ltil K η := by
  unfold Ltil
  have := mul_nonneg hK (by linarith : 0 ≤ 1 + 2 * η)
  linarith

lemma CPi_pos {c4 c5 : ℝ} (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5) : 0 < CPi c4 c5 := by
  unfold CPi
  linarith

lemma C0_nonneg {K η σ : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η) (hσ : 0 < σ) : 0 ≤ C0 K η σ := by
  have := Ltil_pos hK hη
  unfold C0
  positivity

lemma C1_nonneg {K η σ c4 c5 : ℝ} (hK : 0 ≤ K) (hη : 0 ≤ η) (hσ : 0 < σ) (hc4 : 0 ≤ c4)
    (hc5 : 0 ≤ c5) : 0 ≤ C1 K η σ c4 c5 := by
  unfold C1
  exact add_nonneg (CPi_pos hc4 hc5).le (C0_nonneg hK hη hσ)

lemma C1_eq (K η σ c4 c5 : ℝ) :
    C1 K η σ c4 c5 =
      CPi c4 c5 + (Real.sqrt 2 * Ltil K η / σ + Ltil K η ^ 2 / (2 * σ ^ 2)) := by
  rfl

lemma one_le_Aconst {K η σ μ c4 c5 : ℝ} (hμ : 0 < μ) (hC1 : 0 ≤ C1 K η σ c4 c5) :
    1 ≤ Aconst K η σ μ c4 c5 := by
  unfold Aconst
  exact Nat.ceil_pos.2 (div_pos (by linarith) hμ)

lemma le_mu_mul_Aconst {K η σ μ c4 c5 : ℝ} (hμ : 0 < μ) :
    C1 K η σ c4 c5 + 1 ≤ μ * Aconst K η σ μ c4 c5 := by
  have h := Nat.le_ceil ((C1 K η σ c4 c5 + 1) / μ)
  rw [div_le_iff₀ hμ] at h
  unfold Aconst
  linarith

/-! ## Measurability of the sets of the theorem -/

lemma measurableSet_farSet (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (r : ℝ) :
    MeasurableSet (farSet X f₀ r) := by
  have hc : Continuous fun θ : Fin J → ℝ => empNorm (X *ᵥ θ - f₀) :=
    continuous_empNorm.comp ((continuous_const.matrix_mulVec continuous_id).sub continuous_const)
  exact (isOpen_lt continuous_const hc).measurableSet

lemma measurableSet_denseSet (δ : ℝ) (m : ℕ) : MeasurableSet (denseSet (J := J) δ m) := by
  have hmeas : Measurable (numLarge (J := J) δ) := by
    have : numLarge (J := J) δ = fun θ => ∑ j, if δ < |θ j| then 1 else 0 := by
      funext θ
      rw [numLarge, Finset.card_filter]
    rw [this]
    refine Finset.measurable_sum _ fun j _ => Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const ((measurable_pi_apply j).abs)
  exact hmeas measurableSet_Ioi

end LargePrior
