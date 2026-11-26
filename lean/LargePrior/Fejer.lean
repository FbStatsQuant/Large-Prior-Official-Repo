import LargePrior.TrigBasics

/-!
# The Fejér kernel in real form (`eq:fejer-kernel`)
-/

open MeasureTheory Finset intervalIntegral
open scoped Real

noncomputable section

namespace LargePrior

/-- Fejér kernel in real form: `F_N(u) = 1 + 2 ∑_{j=1}^{N} (1 − j/(N+1)) cos(2πju)`. -/
def fejerKernel (N : ℕ) (u : ℝ) : ℝ :=
  1 + 2 * ∑ j ∈ Icc 1 N, (1 - (j : ℝ) / (N + 1)) * Real.cos (2 * π * j * u)

private lemma sum_range_sub_eq_sum_Icc (f : ℝ → ℝ) (n : ℕ) :
    ∑ v ∈ range n, f ((n : ℝ) - v) = ∑ j ∈ Icc 1 n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ', sum_Icc_succ_top (by omega), ← ih]
    congr 1
    · refine sum_congr rfl fun i _ => ?_
      congr 1
      push_cast
      ring
    · simp

/-- `(N+1) F_N(u)` written out: `(N+1) + 2 ∑_{j=1}^N (N+1−j) cos 2πju`. -/
private def fejerNum (N : ℕ) (u : ℝ) : ℝ :=
  ((N : ℝ) + 1) + 2 * ∑ j ∈ Icc 1 N, ((N : ℝ) + 1 - j) * Real.cos (2 * π * j * u)

private lemma mul_fejerKernel_eq (N : ℕ) (u : ℝ) :
    ((N : ℝ) + 1) * fejerKernel N u = fejerNum N u := by
  have hN : ((N : ℝ) + 1) ≠ 0 := by positivity
  unfold fejerKernel fejerNum
  rw [mul_add, mul_one, mul_left_comm, mul_sum]
  congr 2
  refine sum_congr rfl fun j _ => ?_
  field_simp

private lemma fejerNum_succ (N : ℕ) (u : ℝ) :
    fejerNum (N + 1) u =
      fejerNum N u + 1 + 2 * ∑ j ∈ Icc 1 (N + 1), Real.cos (2 * π * j * u) := by
  have h : ∑ j ∈ Icc 1 N, (((N + 1 : ℕ) : ℝ) + 1 - j) * Real.cos (2 * π * j * u) =
      ∑ j ∈ Icc 1 N, ((N : ℝ) + 1 - j) * Real.cos (2 * π * j * u) +
        ∑ j ∈ Icc 1 N, Real.cos (2 * π * j * u) := by
    rw [← sum_add_distrib]
    refine sum_congr rfl fun j _ => ?_
    push_cast
    ring
  unfold fejerNum
  rw [sum_Icc_succ_top (by omega), sum_Icc_succ_top (by omega), h]
  push_cast
  ring

private lemma cross_sum (N : ℕ) (u : ℝ) :
    (∑ v ∈ range (N + 1), Real.cos (2 * π * v * u)) * Real.cos (2 * π * ((N + 1 : ℕ) : ℝ) * u) +
      (∑ v ∈ range (N + 1), Real.sin (2 * π * v * u)) *
        Real.sin (2 * π * ((N + 1 : ℕ) : ℝ) * u) =
      ∑ j ∈ Icc 1 (N + 1), Real.cos (2 * π * j * u) := by
  rw [← sum_range_sub_eq_sum_Icc (fun y => Real.cos (2 * π * y * u)), sum_mul, sum_mul,
    ← sum_add_distrib]
  refine sum_congr rfl fun v _ => ?_
  have : 2 * π * (((N + 1 : ℕ) : ℝ) - v) * u =
      2 * π * ((N + 1 : ℕ) : ℝ) * u - 2 * π * v * u := by ring
  rw [this, Real.cos_sub]
  ring

/-- Sum-of-squares form: `(N+1) F_N(u) = (∑_{v=0}^{N} cos 2πvu)² + (∑_{v=0}^{N} sin 2πvu)²`. -/
lemma fejerKernel_sumsq (N : ℕ) (u : ℝ) :
    ((N : ℝ) + 1) * fejerKernel N u =
      (∑ v ∈ range (N + 1), Real.cos (2 * π * v * u)) ^ 2 +
        (∑ v ∈ range (N + 1), Real.sin (2 * π * v * u)) ^ 2 := by
  rw [mul_fejerKernel_eq]
  induction N with
  | zero => simp [fejerNum]
  | succ N ih =>
    rw [fejerNum_succ, ih, sum_range_succ _ (N + 1), sum_range_succ _ (N + 1), ← cross_sum]
    have h1 := Real.sin_sq_add_cos_sq (2 * π * ((N + 1 : ℕ) : ℝ) * u)
    linear_combination -h1

/-- The Fejér kernel is nonnegative:
`(N+1) F_N(u) = (∑_{v=0}^{N} cos 2πvu)² + (∑_{v=0}^{N} sin 2πvu)²`. -/
lemma fejerKernel_nonneg (N : ℕ) (u : ℝ) : 0 ≤ fejerKernel N u := by
  have h := fejerKernel_sumsq N u
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have : 0 ≤ ((N : ℝ) + 1) * fejerKernel N u := by rw [h]; positivity
  exact (mul_nonneg_iff_of_pos_left hN).1 this

/-- `∫₀¹ cos(2πjs) ds = 0` for `j ≥ 1`. -/
private lemma integral_cos_two_pi_nat {j : ℕ} (hj : 1 ≤ j) :
    ∫ s in (0 : ℝ)..1, Real.cos (2 * π * j * s) = 0 := by
  have hc : (2 * π * j : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ j := by exact_mod_cast hj
    have := Real.pi_pos
    positivity
  rw [intervalIntegral.integral_comp_mul_left (fun s => Real.cos s) hc, integral_cos]
  have : Real.sin (2 * π * j) = 0 := by
    rw [show 2 * π * j = ((2 * j : ℕ) : ℝ) * π by push_cast; ring]
    exact Real.sin_nat_mul_pi _
  simp [this]

/-- For `j ≥ 1`: `∫₀¹ cos(2πj(x − t)) dt = 0`. -/
private lemma integral_cos_two_pi_nat_sub {j : ℕ} (hj : 1 ≤ j) (x : ℝ) :
    ∫ t in (0 : ℝ)..1, Real.cos (2 * π * j * (x - t)) = 0 := by
  have hper : Function.Periodic (fun s : ℝ => Real.cos (2 * π * j * s)) 1 := by
    intro s
    simp only
    rw [show 2 * π * j * (s + 1) = 2 * π * j * s + (j : ℕ) * (2 * π) by ring,
      Real.cos_add_nat_mul_two_pi]
  rw [intervalIntegral.integral_comp_sub_left (fun s => Real.cos (2 * π * j * s)) x,
    show x - 0 = (x - 1) + 1 by ring, hper.intervalIntegral_add_eq (x - 1) 0, zero_add]
  exact integral_cos_two_pi_nat hj

/-- Unit mass in either variable: `∫₀¹ F_N(x − t) dt = 1`. -/
lemma integral_fejerKernel_sub (N : ℕ) (x : ℝ) :
    ∫ t in (0 : ℝ)..1, fejerKernel N (x - t) = 1 := by
  have hcont : ∀ j : ℕ, Continuous fun t : ℝ => Real.cos (2 * π * j * (x - t)) := by
    intro j; fun_prop
  unfold fejerKernel
  rw [intervalIntegral.integral_add intervalIntegrable_const
      ((by fun_prop : Continuous fun t : ℝ => 2 * ∑ j ∈ Icc 1 N,
        (1 - (j : ℝ) / (N + 1)) * Real.cos (2 * π * j * (x - t))).intervalIntegrable 0 1),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_finsetSum
      (fun j _ => ((hcont j).const_mul _).intervalIntegrable 0 1)]
  have h0 : ∀ j ∈ Icc 1 N, ∫ t in (0 : ℝ)..1,
      (1 - (j : ℝ) / (N + 1)) * Real.cos (2 * π * j * (x - t)) = 0 := by
    intro j hj
    rw [intervalIntegral.integral_const_mul, integral_cos_two_pi_nat_sub (mem_Icc.1 hj).1, mul_zero]
  rw [sum_eq_zero h0]
  simp

lemma continuous_fejerKernel (N : ℕ) : Continuous (fejerKernel N) := by
  unfold fejerKernel
  fun_prop

end LargePrior
