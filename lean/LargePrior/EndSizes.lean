import LargePrior.SplineBook

/-!
# Dictionary sizes for the end-to-end corollaries (blueprint §E, first lemma)
-/

open Filter Finset

noncomputable section

namespace LargePrior

private lemma sizes_of_pointwise {d : ℕ} {b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {c C : ℝ} (hc : 0 < c) (hc1 : c ≤ 1) (hC1 : 1 ≤ C)
    (hJ : ∀ n, (J n : ℝ) = ∏ k, (L n k : ℝ))
    (hL : ∀ᶠ n : ℕ in atTop, ∀ k, c * (n : ℝ) ^ b k ≤ L n k ∧ (L n k : ℝ) ≤ C * (n : ℝ) ^ b k) :
    SizesComparable b L J := by
  refine ⟨c, C, hc, ?_⟩
  filter_upwards [hL] with n hn
  have hP : 0 ≤ ∏ k, (L n k : ℝ) := Finset.prod_nonneg (fun k _ => Nat.cast_nonneg _)
  refine ⟨hn, ?_, ?_⟩
  · rw [hJ n]; nlinarith
  · rw [hJ n]; nlinarith

private lemma one_le_rpow_nat {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 < x) :
    1 ≤ (n : ℝ) ^ x :=
  Real.one_le_rpow (by exact_mod_cast hn) hx.le

/-- Fourier sizes: `L_{n,k} = 2⌈n^{b_k}⌉ + 1 ≍ n^{b_k}` and `J_n = ∏_k L_{n,k}` (blueprint E.1). -/
lemma fourier_sizes {d : ℕ} {b : Fin d → ℝ} (hb : ∀ k, 0 < b k) :
    SizesComparable b (fun n k => 2 * fourierM b n k + 1) (fourierJ b) := by
  refine sizes_of_pointwise (c := 1) (C := 5) one_pos le_rfl (by norm_num) ?_ ?_
  · intro n
    simp only [fourierJ, Fintype.card_pi, Fintype.card_fin]
    push_cast
    rfl
  · filter_upwards [eventually_ge_atTop 1] with n hn k
    have h1 := one_le_rpow_nat hn (hb k)
    have h2 := Nat.le_ceil ((n : ℝ) ^ b k)
    have h3 := Nat.ceil_lt_add_one (by linarith : 0 ≤ (n : ℝ) ^ b k)
    simp only [fourierM]
    push_cast
    constructor <;> nlinarith

private lemma sum_pow_two_lt (H : ℕ) : ∑ ℓ ∈ range (H + 1), 2 ^ ℓ < 2 ^ (H + 1) := by
  have hsum := geom_sum_mul_of_one_le (by decide : 1 ≤ (2 : ℕ)) (H + 1)
  norm_num only [Nat.reduceSub, mul_one] at hsum
  have hpow : 1 ≤ 2 ^ (H + 1) := Nat.one_le_two_pow
  omega

private lemma splineUnionDim_le' {q : ℕ} (hq : 1 ≤ q) (H : ℕ) :
    splineUnionDim q H ≤ q * 2 ^ (H + 1) := by
  have h1 : splineUnionDim q H ≤ ∑ ℓ ∈ range (H + 1), q * 2 ^ ℓ := by
    apply Finset.sum_le_sum
    intro ℓ _
    have : 1 ≤ 2 ^ ℓ := Nat.one_le_two_pow
    simp only [splineDim]
    obtain ⟨p, rfl⟩ : ∃ p, q = p + 1 := ⟨q - 1, by omega⟩
    have : p ≤ p * 2 ^ ℓ := Nat.le_mul_of_pos_right p this
    rw [add_mul, one_mul]
    omega
  rw [← Finset.mul_sum] at h1
  have := sum_pow_two_lt H
  calc _ ≤ _ := h1
    _ ≤ q * 2 ^ (H + 1) := Nat.mul_le_mul_left _ this.le

private lemma two_pow_le_splineUnionDim {q : ℕ} (hq : 1 ≤ q) (H : ℕ) : 2 ^ H ≤ splineUnionDim q H := by
  have : splineDim q H ≤ splineUnionDim q H :=
    Finset.single_le_sum (f := fun ℓ => splineDim q ℓ) (fun _ _ => Nat.zero_le _)
      (Finset.self_mem_range_succ H)
  simp only [splineDim] at this
  omega

private lemma rpow_le_two_pow_ceil {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x) :
    (n : ℝ) ^ x ≤ (2 : ℝ) ^ ⌈x * Real.logb 2 n⌉₊ ∧
    (2 : ℝ) ^ ⌈x * Real.logb 2 n⌉₊ ≤ 2 * (n : ℝ) ^ x := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have key : (n : ℝ) ^ x = (2 : ℝ) ^ (x * Real.logb 2 n) := by
    conv_lhs => rw [← Real.rpow_logb (b := 2) (by norm_num) (by norm_num) hn0]
    rw [← Real.rpow_mul (by norm_num), mul_comm]
  have hle := Nat.le_ceil (x * Real.logb 2 n)
  have hlog : 0 ≤ Real.logb 2 n :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast hn)
  have hlt := Nat.ceil_lt_add_one (mul_nonneg hx hlog)
  constructor
  · rw [key]
    calc (2 : ℝ) ^ (x * Real.logb 2 n) ≤ (2 : ℝ) ^ ((⌈x * Real.logb 2 n⌉₊ : ℕ) : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hle
      _ = _ := Real.rpow_natCast _ _
  · rw [key]
    calc (2 : ℝ) ^ ⌈x * Real.logb 2 n⌉₊
        = (2 : ℝ) ^ ((⌈x * Real.logb 2 n⌉₊ : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
      _ ≤ (2 : ℝ) ^ (x * Real.logb 2 n + 1) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hlt.le
      _ = 2 * (2 : ℝ) ^ (x * Real.logb 2 n) := by
          rw [Real.rpow_add (by norm_num), Real.rpow_one, mul_comm]

/-- Spline sizes: `L_{n,k} = U_{H_{n,k}} ≍ n^{b_k}` with `H_{n,k} = ⌈b_k log₂ n⌉`, and
`J_n = ∏_k L_{n,k}` (blueprint E.1). -/
lemma spline_sizes {d q : ℕ} (hq : 1 ≤ q) {b : Fin d → ℝ} (hb : ∀ k, 0 < b k) :
    SizesComparable b (fun n k => splineUnionDim q (splineH b n k)) (splineJ q b) := by
  refine sizes_of_pointwise (c := 1) (C := 4 * q) one_pos le_rfl ?_ ?_ ?_
  · have : (1 : ℝ) ≤ q := by exact_mod_cast hq
    linarith
  · intro n
    simp only [splineJ, Fintype.card_pi, Fintype.card_sigma, Fintype.card_fin]
    push_cast
    refine Finset.prod_congr rfl (fun k _ => ?_)
    rw [← Nat.cast_sum, Fin.sum_univ_eq_sum_range (fun ℓ => splineDim q ℓ) (splineH b n k + 1)]
    rfl
  · filter_upwards [eventually_ge_atTop 1] with n hn k
    obtain ⟨h1, h2⟩ := rpow_le_two_pow_ceil hn (x := b k) (hb k).le
    have h3 : ((2 ^ splineH b n k : ℕ) : ℝ) ≤ splineUnionDim q (splineH b n k) := by
      exact_mod_cast two_pow_le_splineUnionDim hq _
    have h4 : (splineUnionDim q (splineH b n k) : ℝ) ≤ q * 2 ^ (splineH b n k + 1) := by
      exact_mod_cast splineUnionDim_le' hq _
    have hH : (2 : ℝ) ^ splineH b n k ≤ 2 * (n : ℝ) ^ b k := h2
    have hH' : (n : ℝ) ^ b k ≤ (2 : ℝ) ^ splineH b n k := h1
    push_cast at h3
    have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg _
    rw [pow_succ] at h4
    constructor
    · linarith
    · nlinarith

end LargePrior
