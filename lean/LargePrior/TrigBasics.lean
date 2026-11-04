import LargePrior.CorSpec

/-!
# Trigonometric facts for the Fourier lemma (blueprint §F.1)

Orthonormality of the real atoms on `[0,1]`, their `L¹` bound, the pairing identity, and the
pairing reindex of sums over atoms.
-/

open MeasureTheory Finset intervalIntegral
open scoped Real

noncomputable section

namespace LargePrior

/-- Frequency of the atom `ψ_ν`: `j(0) = 0`, `j(2j−1) = j(2j) = j`. -/
def freq (ν : ℕ) : ℕ := (ν + 1) / 2

/-! ### Helpers: representation of the atoms through `freq`, and the basic integrals -/

private lemma fourierAtom_eq_zero_case : fourierAtom 0 = fun _ => 1 := by
  funext x; simp [fourierAtom]

private lemma fourierAtom_eq_odd {ν : ℕ} (h : ν % 2 = 1) :
    fourierAtom ν = fun x => Real.sqrt 2 * Real.cos (2 * π * (freq ν : ℝ) * x) := by
  funext x
  have h0 : ν ≠ 0 := by omega
  simp [fourierAtom, h0, h, freq]

private lemma fourierAtom_eq_even {ν : ℕ} (h0 : ν ≠ 0) (h : ν % 2 = 0) :
    fourierAtom ν = fun x => Real.sqrt 2 * Real.sin (2 * π * (freq ν : ℝ) * x) := by
  funext x
  have h1 : ¬ ν % 2 = 1 := by omega
  have h2 : ν / 2 = (ν + 1) / 2 := by omega
  simp only [fourierAtom, h0, h1, ↓reduceIte, freq, h2]

private lemma atom_cases (ν : ℕ) :
    ν = 0 ∨ (ν % 2 = 1 ∧ 1 ≤ freq ν) ∨ (ν ≠ 0 ∧ ν % 2 = 0 ∧ 1 ≤ freq ν) := by
  unfold freq; omega

private lemma sqrt_two_mul_self' : Real.sqrt 2 * Real.sqrt 2 = 2 :=
  Real.mul_self_sqrt (by norm_num)

private lemma integral_cos_int (ℓ : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * ℓ * x) = if ℓ = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp
  · have hℓ : (ℓ : ℝ) ≠ 0 := by exact_mod_cast h
    have hc : (2 * π * ℓ : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hℓ
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x) hc, integral_cos]
    have : Real.sin (2 * π * ℓ) = 0 := by
      rw [show (2 * π * ℓ : ℝ) = ((2 * ℓ : ℤ) : ℝ) * π by push_cast; ring]
      exact Real.sin_int_mul_pi _
    simp [this]

private lemma integral_sin_int (ℓ : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * π * ℓ * x) = 0 := by
  by_cases h : ℓ = 0
  · subst h; simp
  · have hℓ : (ℓ : ℝ) ≠ 0 := by exact_mod_cast h
    have hc : (2 * π * ℓ : ℝ) ≠ 0 := mul_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero) hℓ
    rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x) hc, integral_sin]
    have : Real.cos (2 * π * ℓ) = 1 := by
      rw [show (2 * π * ℓ : ℝ) = (ℓ : ℝ) * (2 * π) by ring]
      exact Real.cos_int_mul_two_pi _
    simp [this]

private lemma integral_cos_nat {k : ℕ} (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * k * x) = 0 := by
  have h := integral_cos_int k
  have hk' : k ≠ 0 := by omega
  simpa [hk'] using h

private lemma integral_sin_nat (k : ℕ) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * π * k * x) = 0 := by
  simpa using integral_sin_int k

private lemma integral_cos_mul_cos {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * j * x) * Real.cos (2 * π * k * x) =
      if j = k then 1 / 2 else 0 := by
  have h : ∀ x : ℝ, Real.cos (2 * π * j * x) * Real.cos (2 * π * k * x) =
      (Real.cos (2 * π * (((j : ℤ) - k : ℤ) : ℝ) * x) +
        Real.cos (2 * π * (((j : ℤ) + k : ℤ) : ℝ) * x)) / 2 := by
    intro x; push_cast
    rw [show 2 * π * ((j : ℝ) - k) * x = 2 * π * j * x - 2 * π * k * x by ring,
      show 2 * π * ((j : ℝ) + k) * x = 2 * π * j * x + 2 * π * k * x by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), integral_cos_int, integral_cos_int]
  have h2 : ((j : ℤ) + k) ≠ 0 := by omega
  by_cases hjk : j = k
  · subst hjk; simp [h2]
  · have h3 : ((j : ℤ) - k) ≠ 0 := by omega
    simp [hjk, h2, h3]

private lemma integral_sin_mul_sin {j k : ℕ} (hj : 1 ≤ j) (hk : 1 ≤ k) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * π * j * x) * Real.sin (2 * π * k * x) =
      if j = k then 1 / 2 else 0 := by
  have h : ∀ x : ℝ, Real.sin (2 * π * j * x) * Real.sin (2 * π * k * x) =
      (Real.cos (2 * π * (((j : ℤ) - k : ℤ) : ℝ) * x) -
        Real.cos (2 * π * (((j : ℤ) + k : ℤ) : ℝ) * x)) / 2 := by
    intro x; push_cast
    rw [show 2 * π * ((j : ℝ) - k) * x = 2 * π * j * x - 2 * π * k * x by ring,
      show 2 * π * ((j : ℝ) + k) * x = 2 * π * j * x + 2 * π * k * x by ring,
      Real.cos_sub, Real.cos_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_sub (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), integral_cos_int, integral_cos_int]
  have h2 : ((j : ℤ) + k) ≠ 0 := by omega
  by_cases hjk : j = k
  · subst hjk; simp [h2]
  · have h3 : ((j : ℤ) - k) ≠ 0 := by omega
    simp [hjk, h2, h3]

private lemma integral_sin_mul_cos (j k : ℕ) :
    ∫ x in (0 : ℝ)..1, Real.sin (2 * π * j * x) * Real.cos (2 * π * k * x) = 0 := by
  have h : ∀ x : ℝ, Real.sin (2 * π * j * x) * Real.cos (2 * π * k * x) =
      (Real.sin (2 * π * (((j : ℤ) + k : ℤ) : ℝ) * x) +
        Real.sin (2 * π * (((j : ℤ) - k : ℤ) : ℝ) * x)) / 2 := by
    intro x; push_cast
    rw [show 2 * π * ((j : ℝ) - k) * x = 2 * π * j * x - 2 * π * k * x by ring,
      show 2 * π * ((j : ℝ) + k) * x = 2 * π * j * x + 2 * π * k * x by ring,
      Real.sin_sub, Real.sin_add]
    ring
  simp_rw [h]
  rw [intervalIntegral.integral_div,
    intervalIntegral.integral_add (Continuous.intervalIntegrable (by fun_prop) _ _)
      (Continuous.intervalIntegrable (by fun_prop) _ _), integral_sin_int, integral_sin_int]
  simp

private lemma integral_cos_mul_sin (j k : ℕ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * j * x) * Real.sin (2 * π * k * x) = 0 := by
  have h : ∀ x : ℝ, Real.cos (2 * π * j * x) * Real.sin (2 * π * k * x) =
      Real.sin (2 * π * k * x) * Real.cos (2 * π * j * x) := fun x => mul_comm _ _
  simp_rw [h]
  exact integral_sin_mul_cos k j

/-- `∫₀¹ (√2 f)(√2 g) = 2 ∫₀¹ f g`. -/
private lemma integral_sqrt_two_mul {f g : ℝ → ℝ} :
    ∫ x in (0 : ℝ)..1, Real.sqrt 2 * f x * (Real.sqrt 2 * g x) =
      2 * ∫ x in (0 : ℝ)..1, f x * g x := by
  have h : ∀ x, Real.sqrt 2 * f x * (Real.sqrt 2 * g x) = 2 * (f x * g x) := by
    intro x; linear_combination (f x * g x) * sqrt_two_mul_self'
  simp_rw [h]
  exact intervalIntegral.integral_const_mul _ _

private lemma freq_inj_odd {ν μ : ℕ} (hν : ν % 2 = 1) (hμ : μ % 2 = 1) :
    freq ν = freq μ ↔ ν = μ := by
  unfold freq; omega

private lemma freq_inj_even {ν μ : ℕ} (hν : ν % 2 = 0) (hμ : μ % 2 = 0) :
    freq ν = freq μ ↔ ν = μ := by
  unfold freq; omega

lemma continuous_fourierAtom (ν : ℕ) : Continuous (fourierAtom ν) := by
  rcases atom_cases ν with h | ⟨h, -⟩ | ⟨h0, h, -⟩
  · subst h; rw [fourierAtom_eq_zero_case]; exact continuous_const
  · rw [fourierAtom_eq_odd h]; fun_prop
  · rw [fourierAtom_eq_even h0 h]; fun_prop

/-- `ψ_ν = √2 cos(2π j(ν) x)` or `√2 sin(2π j(ν) x)` or `1`; in particular 1-periodic. -/
lemma fourierAtom_periodic (ν : ℕ) : Function.Periodic (fourierAtom ν) 1 := by
  intro x
  have hx : 2 * π * (freq ν : ℝ) * (x + 1) = 2 * π * (freq ν : ℝ) * x + (freq ν : ℕ) * (2 * π) := by
    ring
  rcases atom_cases ν with h | ⟨h, -⟩ | ⟨h0, h, -⟩
  · subst h; simp [fourierAtom_eq_zero_case]
  · rw [fourierAtom_eq_odd h]; simp only [hx, Real.cos_add_nat_mul_two_pi]
  · rw [fourierAtom_eq_even h0 h]; simp only [hx, Real.sin_add_nat_mul_two_pi]

/-- Orthonormality on `[0,1]`: `∫₀¹ ψ_ν ψ_μ = 1` if `ν = μ`, else `0`. -/
lemma integral_fourierAtom_mul (ν μ : ℕ) :
    ∫ t in (0 : ℝ)..1, fourierAtom ν t * fourierAtom μ t = if ν = μ then 1 else 0 := by
  rcases atom_cases ν with hν | ⟨hν, hν1⟩ | ⟨hν0, hν, hν1⟩ <;>
    rcases atom_cases μ with hμ | ⟨hμ, hμ1⟩ | ⟨hμ0, hμ, hμ1⟩
  · subst hν hμ; simp [fourierAtom_eq_zero_case]
  · subst hν
    have hne : (0 : ℕ) ≠ μ := by omega
    rw [fourierAtom_eq_zero_case, fourierAtom_eq_odd hμ]
    simp only [one_mul, hne, ↓reduceIte]
    rw [intervalIntegral.integral_const_mul, integral_cos_nat hμ1, mul_zero]
  · subst hν
    have hne : (0 : ℕ) ≠ μ := by omega
    rw [fourierAtom_eq_zero_case, fourierAtom_eq_even hμ0 hμ]
    simp only [one_mul, hne, ↓reduceIte]
    rw [intervalIntegral.integral_const_mul, integral_sin_nat, mul_zero]
  · subst hμ
    have hne : ν ≠ 0 := by omega
    rw [fourierAtom_eq_zero_case, fourierAtom_eq_odd hν]
    simp only [mul_one, hne, ↓reduceIte]
    rw [intervalIntegral.integral_const_mul, integral_cos_nat hν1, mul_zero]
  · rw [fourierAtom_eq_odd hν, fourierAtom_eq_odd hμ]
    simp only
    rw [integral_sqrt_two_mul, integral_cos_mul_cos hν1 hμ1]
    simp only [freq_inj_odd hν hμ]
    split_ifs <;> norm_num
  · have hne : ν ≠ μ := by omega
    rw [fourierAtom_eq_odd hν, fourierAtom_eq_even hμ0 hμ]
    simp only [hne, ↓reduceIte]
    rw [integral_sqrt_two_mul, integral_cos_mul_sin, mul_zero]
  · subst hμ
    have hne : ν ≠ 0 := by omega
    rw [fourierAtom_eq_zero_case, fourierAtom_eq_even hν0 hν]
    simp only [mul_one, hne, ↓reduceIte]
    rw [intervalIntegral.integral_const_mul, integral_sin_nat, mul_zero]
  · have hne : ν ≠ μ := by omega
    rw [fourierAtom_eq_even hν0 hν, fourierAtom_eq_odd hμ]
    simp only [hne, ↓reduceIte]
    rw [integral_sqrt_two_mul, integral_sin_mul_cos, mul_zero]
  · rw [fourierAtom_eq_even hν0 hν, fourierAtom_eq_even hμ0 hμ]
    simp only
    rw [integral_sqrt_two_mul, integral_sin_mul_sin hν1 hμ1]
    simp only [freq_inj_even hν hμ]
    split_ifs <;> norm_num

/-- `∫₀¹ |ψ_ν| ≤ 1`. -/
lemma integral_abs_fourierAtom_le (ν : ℕ) : ∫ t in (0 : ℝ)..1, |fourierAtom ν t| ≤ 1 := by
  have hc := continuous_fourierAtom ν
  have hle : ∀ t, |fourierAtom ν t| ≤ (1 + fourierAtom ν t * fourierAtom ν t) / 2 := by
    intro t
    have h1 := sq_nonneg (|fourierAtom ν t| - 1)
    have h2 : |fourierAtom ν t| * |fourierAtom ν t| = fourierAtom ν t * fourierAtom ν t :=
      abs_mul_abs_self _
    nlinarith
  calc ∫ t in (0 : ℝ)..1, |fourierAtom ν t|
      ≤ ∫ t in (0 : ℝ)..1, (1 + fourierAtom ν t * fourierAtom ν t) / 2 :=
        intervalIntegral.integral_mono_on zero_le_one (hc.abs.intervalIntegrable _ _)
          (((continuous_const.add (hc.mul hc)).div_const 2).intervalIntegrable _ _)
          (fun t _ => hle t)
    _ = 1 := by
        rw [intervalIntegral.integral_div,
          intervalIntegral.integral_add (f := fun _ => (1 : ℝ))
            (g := fun x => fourierAtom ν x * fourierAtom ν x)
            (continuous_const.intervalIntegrable _ _)
            ((hc.mul hc).intervalIntegrable _ _), integral_fourierAtom_mul]
        norm_num

/-- Pairing identity: for `j ≥ 1`,
`ψ_{2j−1}(x) ψ_{2j−1}(t) + ψ_{2j}(x) ψ_{2j}(t) = 2 cos(2πj(x − t))`. -/
lemma fourierAtom_pair {j : ℕ} (hj : 1 ≤ j) (x t : ℝ) :
    fourierAtom (2 * j - 1) x * fourierAtom (2 * j - 1) t +
      fourierAtom (2 * j) x * fourierAtom (2 * j) t = 2 * Real.cos (2 * π * j * (x - t)) := by
  have hodd : (2 * j - 1) % 2 = 1 := by omega
  have h0 : 2 * j ≠ 0 := by omega
  have hev : (2 * j) % 2 = 0 := by omega
  have f1 : freq (2 * j - 1) = j := by unfold freq; omega
  have f2 : freq (2 * j) = j := by unfold freq; omega
  rw [fourierAtom_eq_odd hodd, fourierAtom_eq_even h0 hev]
  simp only [f1, f2]
  rw [show 2 * π * (j : ℝ) * (x - t) = 2 * π * j * x - 2 * π * j * t by ring, Real.cos_sub]
  linear_combination (Real.cos (2 * π * j * x) * Real.cos (2 * π * j * t) +
    Real.sin (2 * π * j * x) * Real.sin (2 * π * j * t)) * sqrt_two_mul_self'

/-- `freq (2j − 1) = freq (2j) = j` for `j ≥ 1`, and `freq 0 = 0`. -/
lemma freq_spec {j : ℕ} (hj : 1 ≤ j) : freq (2 * j - 1) = j ∧ freq (2 * j) = j := by
  unfold freq; omega

/-- Pairing reindex: `∑_{ν < 2N+1} F ν = F 0 + ∑_{j=1}^{N} (F (2j−1) + F (2j))`. -/
lemma sum_range_pair (N : ℕ) (F : ℕ → ℝ) :
    ∑ ν ∈ range (2 * N + 1), F ν = F 0 + ∑ j ∈ Icc 1 N, (F (2 * j - 1) + F (2 * j)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) + 1 = 2 * n + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_Icc_succ_top (by omega : 1 ≤ n + 1),
      show 2 * (n + 1) - 1 = 2 * n + 1 by omega, show 2 * (n + 1) = 2 * n + 1 + 1 by ring]
    ring

end LargePrior
