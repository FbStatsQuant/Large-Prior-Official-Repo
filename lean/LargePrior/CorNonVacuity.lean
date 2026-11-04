import LargePrior.EndToEnd

/-!
# Non-vacuity, Fourier side (blueprint §N)

Concrete instances (`d = 1`, `α = 1`, `b = 1`, design `x_i = i/n`):
* `CorHorseshoeHyp` (hence `CorHyp`) for the Fourier dictionary and `f₀ = ψ₁`;
* `CorFourierHyp` for `f₀ = ψ₁` (Hölder–Zygmund ball of order 1, difference order 2, radius 30).
-/

open MeasureTheory Filter Finset
open scoped Topology Matrix

noncomputable section

namespace LargePrior

/-- Design points `x_i = i/n` in `[0,1]` (one coordinate). -/
def nvDesign (n : ℕ) (i : Fin n) : Fin 1 → ℝ := fun _ => (i : ℝ) / n

/-- The design `x_i = i/n` lies in `[0,1]`. -/
lemma nvDesign_mem (n : ℕ) (i : Fin n) : nvDesign n i ∈ unitCube 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero fun h => by subst h; exact i.elim0
  have hi : (i : ℝ) ≤ n := by exact_mod_cast i.isLt.le
  intro k
  exact ⟨div_nonneg (Nat.cast_nonneg _) hn.le, (div_le_one hn).2 hi⟩

/-- `f₀ = ψ₁`, i.e. `√2 cos(2πx)`, on `ℝ¹`. -/
def nvPsi1 (y : Fin 1 → ℝ) : ℝ := fourierAtom 1 (y 0)

/-- `ψ₁(t) = √2 cos(2πt)`. -/
private lemma fourierAtom_one_eq (t : ℝ) :
    fourierAtom 1 t = Real.sqrt 2 * Real.cos (2 * Real.pi * t) := by
  simp [fourierAtom]

/-- With `b = 1`, the Fourier dictionary size is `M_n = n`. -/
private lemma nv_fourierM (n : ℕ) (k : Fin 1) : fourierM (fun _ : Fin 1 => (1 : ℝ)) n k = n := by
  simp [fourierM, Real.rpow_one]

/-- The exact one-term profile of `ψ₁` in the Fourier dictionary, for `n ≥ 1`. -/
private lemma nv_prof (n : ℕ) (hn : 1 ≤ n) (m : Fin 1 → ℕ)
    (hm : ∀ k, 1 ≤ m k ∧ m k ≤ 2 * fourierM (fun _ : Fin 1 => (1 : ℝ)) n k + 1) :
    ∃ θ : FourierIdx (fourierM (fun _ : Fin 1 => (1 : ℝ)) n) → ℝ,
      (suppCard θ : ℝ) ≤ ∏ k, (m k : ℝ) ∧
      (∀ y, |nvPsi1 y - fourierSeries θ y| ≤ 0 * 1 * ∑ k, (m k : ℝ) ^ (-(fun _ : Fin 1 => (1 : ℝ)) k)) ∧
      ∀ ν, |θ ν| ≤ 1 := by
  have hlt : ∀ k : Fin 1, 1 < 2 * fourierM (fun _ : Fin 1 => (1 : ℝ)) n k + 1 := fun k => by
    rw [nv_fourierM]; omega
  let ν₁ : FourierIdx (fourierM (fun _ : Fin 1 => (1 : ℝ)) n) := fun k => ⟨1, hlt k⟩
  refine ⟨fun ν => if ν = ν₁ then 1 else 0, ?_, ?_, ?_⟩
  · have hc : suppCard (fun ν => if ν = ν₁ then (1 : ℝ) else 0) ≤ 1 := by
      unfold suppCard
      refine Finset.card_le_one.2 fun a ha b hb => ?_
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at ha hb
      rw [ha, hb]
    have hm0 : (1 : ℝ) ≤ m 0 := by exact_mod_cast (hm 0).1
    rw [Fin.prod_univ_one]
    calc (suppCard (fun ν => if ν = ν₁ then (1 : ℝ) else 0) : ℝ) ≤ 1 := by exact_mod_cast hc
      _ ≤ m 0 := hm0
  · intro y
    simp [fourierSeries, ite_mul, fourierTensor, nvPsi1, ν₁]
  · intro ν
    show |(if ν = ν₁ then (1 : ℝ) else 0)| ≤ 1
    split_ifs <;> simp

/-- **Non-vacuity of `CorHorseshoeHyp`**: Fourier dictionary with `b = 1`, `f₀ = ψ₁`, `α = 1`,
`C_sp = 1`, `C_app = 0`, `E = 2`, `C_ε = 1`, `c_δ = 1/2`, `K = √2`, `η = 1/2`, `μ'' = 1`. -/
theorem corHorseshoe_nonvacuity :
    CorHorseshoeHyp (d := 1) (fun _ => 1) (fun _ => 1)
      (fun n k => 2 * fourierM (fun _ : Fin 1 => (1 : ℝ)) n k + 1)
      (fourierJ fun _ : Fin 1 => (1 : ℝ)) (fourierX (fun _ : Fin 1 => (1 : ℝ)) nvDesign)
      (fun n i => nvPsi1 (nvDesign n i)) 1 1 0 2 1 (1 / 2) (Real.sqrt 2 ^ 1) (1 / 2) 1 := by
  exact
  { hd := one_pos
    hα := fun _ => one_pos
    hb := fun _ => by simp only [betaExp, alphaStar, Nat.cast_one, univ_unique, Fin.default_eq_zero,
      Fin.isValue, inv_one, sum_const, card_singleton, one_smul, ne_eq, one_ne_zero,
      not_false_eq_true, div_self, mul_one, one_mul, one_div]; norm_num
    hsize := fourier_sizes fun _ => one_pos
    hσ := one_pos
    hK := by positivity
    hbasis := Eventually.of_forall fun n => fourier_basisBound _ nvDesign n
    hCsp := one_pos
    hCapp := le_rfl
    hE := two_pos
    hprofile := by
      filter_upwards [Filter.eventually_ge_atTop 1] with n hn
      have h := profileAt_fourier (b := fun _ : Fin 1 => (1 : ℝ)) (x := nvDesign) (f₀ := nvPsi1)
        (α := fun _ => 1) (C := 0) (R := 1) le_rfl zero_le_one n (nv_prof n hn)
      rw [show (0 : ℝ) * 1 = 0 by norm_num, show (1 : ℝ) + 1 = 2 by norm_num] at h
      exact h
    hCeps := one_pos
    hCepsApp := by norm_num
    hcδ := by norm_num
    hcδ1 := by norm_num
    hη := by norm_num
    hη1 := by norm_num
    hμ'' := one_pos }

/-- **Non-vacuity of `CorHyp`** (for the horseshoe prior, through `CorHorseshoeHyp.corHyp`). -/
theorem corHyp_nonvacuity : ∃ c5 : ℝ, 0 ≤ c5 ∧
    CorHyp (d := 1) (fun _ => 1) (fun _ => 1)
      (fun n k => 2 * fourierM (fun _ : Fin 1 => (1 : ℝ)) n k + 1)
      (fourierJ fun _ : Fin 1 => (1 : ℝ)) (fourierX (fun _ : Fin 1 => (1 : ℝ)) nvDesign)
      (fun n i => nvPsi1 (nvDesign n i)) 1
      (fun n => horseshoePDF (corTau 1 n (fourierJ (fun _ : Fin 1 => (1 : ℝ)) n)))
      1 0 2 1 (1 / 2) (Real.sqrt 2 ^ 1) (1 / 2) (1 / 2) 1 c5 :=
  corHorseshoe_nonvacuity.corHyp

/-- Second difference of `ψ₁`: `Δ²_h ψ₁(t) = −4√2 cos(2π(t+h)) sin²(πh)`. -/
private lemma fdiff_two_atom_one (h t : ℝ) :
    fdiff 2 h (fourierAtom 1) t =
      -(4 * Real.sqrt 2 * Real.cos (2 * Real.pi * (t + h)) * Real.sin (Real.pi * h) ^ 2) := by
  simp only [fdiff, Finset.sum_range_succ, Finset.sum_range_zero, fourierAtom_one_eq]
  norm_num
  set u := 2 * Real.pi * (t + h) with hu
  set s := Real.pi * h with hs
  have h1 : 2 * Real.pi * t = u - 2 * s := by rw [hu, hs]; ring
  have h3 : 2 * Real.pi * (t + 2 * h) = u + 2 * s := by rw [hu, hs]; ring
  rw [h1, h3, Real.cos_sub, Real.cos_add, Real.cos_two_mul, Real.sin_two_mul]
  linear_combination (4 * Real.sqrt 2 * Real.cos u) * Real.sin_sq_add_cos_sq s

/-- `|Δ²_h ψ₁(t)| ≤ 28 |h|`. -/
private lemma fdiff_two_atom_one_le (h t : ℝ) : |fdiff 2 h (fourierAtom 1) t| ≤ 28 * |h| := by
  rw [fdiff_two_atom_one, abs_neg]
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsq : Real.sqrt 2 < 1.42 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hc : |Real.cos (2 * Real.pi * (t + h))| ≤ 1 := Real.abs_cos_le_one _
  have hsin1 : |Real.sin (Real.pi * h)| ≤ 1 := Real.abs_sin_le_one _
  have hsin : |Real.sin (Real.pi * h)| ≤ Real.pi * |h| := by
    have := Real.abs_sin_le_abs (x := Real.pi * h)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  have hsq2 : Real.sin (Real.pi * h) ^ 2 ≤ |Real.sin (Real.pi * h)| := by
    rw [← sq_abs]
    nlinarith [abs_nonneg (Real.sin (Real.pi * h))]
  have hpi := Real.pi_lt_d2
  have hh := abs_nonneg h
  rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.sqrt 2),
    abs_of_nonneg (sq_nonneg (Real.sin (Real.pi * h)))]
  calc 4 * Real.sqrt 2 * |Real.cos (2 * Real.pi * (t + h))| * Real.sin (Real.pi * h) ^ 2
      ≤ 4 * Real.sqrt 2 * 1 * (Real.pi * |h|) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hc (by positivity)) (hsq2.trans hsin)
          (sq_nonneg _) (by positivity)
    _ ≤ 28 * |h| := by nlinarith [Real.pi_pos]

/-- **Non-vacuity of `CorFourierHyp`**: `ψ₁` lies in the periodic Hölder–Zygmund ball of order
`1`, difference order `2`, radius `30`. -/
theorem corFourier_nonvacuity :
    CorFourierHyp (d := 1) (fun _ => 1) (fun _ => 1) (fun _ => 2) 30 nvPsi1 1 (1 / 2) 1 := by
  exact
  { hd := one_pos
    hα := fun _ => one_pos
    hr := fun _ => by norm_num
    hb := fun _ => by simp only [betaExp, alphaStar, Nat.cast_one, univ_unique, Fin.default_eq_zero,
      Fin.isValue, inv_one, sum_const, card_singleton, one_smul, ne_eq, one_ne_zero,
      not_false_eq_true, div_self, mul_one, one_mul, one_div]; norm_num
    hball := by
      refine ⟨(continuous_fourierAtom 1).comp (continuous_apply 0), ?_, Real.sqrt 2, 28,
        Real.sqrt_nonneg 2, by norm_num, ?_, fun x => fourierAtom_abs_le 1 (x 0), ?_⟩
      · intro k x
        obtain rfl : k = 0 := Subsingleton.elim k 0
        simp only [nvPsi1, Pi.add_apply, Pi.single_eq_same]
        exact fourierAtom_periodic 1 (x 0)
      · have : Real.sqrt 2 ≤ 2 := by
          rw [Real.sqrt_le_left (by norm_num)]; norm_num
        linarith
      · intro k x h _ _
        obtain rfl : k = 0 := Subsingleton.elim k 0
        have hsec : sectionAt nvPsi1 x 0 = fourierAtom 1 := by
          funext t; simp [sectionAt, nvPsi1]
        rw [hsec, Real.rpow_one]
        exact fdiff_two_atom_one_le h (x 0)
    hσ := one_pos
    hη := by norm_num
    hη1 := by norm_num
    hμ'' := one_pos }

end LargePrior
