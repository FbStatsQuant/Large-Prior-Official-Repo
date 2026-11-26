import LargePrior.Gaussian

/-!
# Lemma 5: the basic Gaussian test (`lem:test`)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

variable {n : ℕ}

/-- Rejection region of `ψ_g`: `{y : ⟨y − f₀, g − f₀⟩ ≥ n d²/2}` with `d = ‖g − f₀‖_{2,n}`. -/
def testRegion (f₀ g : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {y | (n : ℝ) * empNorm (g - f₀) ^ 2 / 2 ≤ ∑ i, (y i - f₀ i) * (g i - f₀ i)}

lemma measurableSet_testRegion (f₀ g : Fin n → ℝ) : MeasurableSet (testRegion f₀ g) := by
  unfold testRegion
  exact measurableSet_le measurable_const (by fun_prop)

/-- **Lemma 5**, type I error: `P₀(R_g) ≤ exp(−n d²/(8σ²))`. -/
theorem basic_test_typeI {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n) {f₀ g : Fin n → ℝ}
    (hd : 0 < empNorm (g - f₀)) :
    dataLaw σ f₀ (testRegion f₀ g) ≤
      ENNReal.ofReal (Real.exp (-(n * empNorm (g - f₀) ^ 2 / (8 * σ ^ 2)))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hsum : ∑ i, (g - f₀) i ^ 2 = n * empNorm (g - f₀) ^ 2 := sum_sq_eq_mul_empNorm_sq hn _
  have h := gauss_lin_upper hσ f₀ (g - f₀) (t := (n : ℝ) * empNorm (g - f₀) ^ 2 / 2)
    (by positivity)
  rw [hsum] at h
  refine le_trans h (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_eq ?_)))
  field_simp
  ring

/-- **Lemma 5**, type II error: `P_v(R_gᶜ) ≤ exp(−n d²/(32σ²))` when `‖v − g‖_{2,n} ≤ d/4`. -/
theorem basic_test_typeII {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n) {f₀ g v : Fin n → ℝ}
    (hd : 0 < empNorm (g - f₀)) (hv : empNorm (v - g) ≤ empNorm (g - f₀) / 4) :
    dataLaw σ v (testRegion f₀ g)ᶜ ≤
      ENNReal.ofReal (Real.exp (-(n * empNorm (g - f₀) ^ 2 / (32 * σ ^ 2)))) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  set d := empNorm (g - f₀) with hdd
  have hsum : ∑ i, (g - f₀) i ^ 2 = n * d ^ 2 := sum_sq_eq_mul_empNorm_sq hn _
  have hsum2 : ∑ i, (v - g) i ^ 2 = n * empNorm (v - g) ^ 2 := sum_sq_eq_mul_empNorm_sq hn _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => (v - g) i) (fun i => (g - f₀) i)
  rw [hsum, hsum2] at hcs
  have he : 0 ≤ empNorm (v - g) := empNorm_nonneg _
  have hb : ((n : ℝ) * d ^ 2 / 4) ^ 2 ≥ (∑ i, (v - g) i * (g - f₀) i) ^ 2 := by
    refine le_trans hcs ?_
    have : empNorm (v - g) ^ 2 ≤ (d / 4) ^ 2 := pow_le_pow_left₀ he hv 2
    nlinarith [mul_le_mul_of_nonneg_left this (le_of_lt (mul_pos hn' (pow_pos hd 2))),
      sq_nonneg d]
  have habs : |∑ i, (v - g) i * (g - f₀) i| ≤ (n : ℝ) * d ^ 2 / 4 :=
    abs_le_of_sq_le_sq' hb (by positivity) |>.elim (fun h1 h2 => abs_le.mpr ⟨h1, h2⟩)
  have hlow := (abs_le.mp habs).1
  have hsplit : ∑ i, (v i - f₀ i) * (g i - f₀ i) =
      n * d ^ 2 + ∑ i, (v - g) i * (g - f₀) i := by
    rw [← hsum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply]; ring
  have hsub : (testRegion f₀ g)ᶜ ⊆ {y | ∑ i, (y i - v i) * (g - f₀) i ≤ -((n : ℝ) * d ^ 2 / 4)} := by
    intro y hy
    simp only [testRegion, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hy
    simp only [Set.mem_ofPred_eq]
    have : ∑ i, (y i - f₀ i) * (g i - f₀ i) =
        ∑ i, (y i - v i) * (g - f₀) i + ∑ i, (v i - f₀ i) * (g i - f₀ i) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Pi.sub_apply]; ring
    linarith
  have h := gauss_lin_lower hσ v (g - f₀) (t := (n : ℝ) * d ^ 2 / 4) (by positivity)
  rw [hsum] at h
  refine le_trans (measure_mono hsub) (le_trans h ?_)
  refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr (le_of_eq ?_))
  field_simp
  ring

end LargePrior
