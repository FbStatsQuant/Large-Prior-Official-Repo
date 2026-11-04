import LargePrior.Basic

/-!
# Assumption 1 from a sup-norm bound; Fourier dictionaries (blueprint Part B)
-/

open MeasureTheory Finset
open scoped Matrix

noncomputable section

namespace LargePrior

variable {n J : ℕ}

/-- A dictionary bounded by `b` on the design satisfies Assumption 1 with `K = b`
(blueprint `lem:basis-of-sup`). -/
lemma basisBound_of_abs_le {𝒳 : Type*} {ξ : Fin J → 𝒳 → ℝ} {x : Fin n → 𝒳} {b : ℝ}
    (hb : 0 ≤ b) (h : ∀ j i, |ξ j (x i)| ≤ b) : BasisBound (designMatrix ξ x) b := by
  intro j
  exact empNorm_le_of_abs_le hb _ fun i => h j i

lemma fourierAtom_abs_le (ν : ℕ) (x : ℝ) : |fourierAtom ν x| ≤ Real.sqrt 2 := by
  have h2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  unfold fourierAtom
  split_ifs
  · simp
  · rw [abs_mul, abs_of_nonneg h2]
    exact mul_le_of_le_one_right h2 (Real.abs_cos_le_one _)
  · rw [abs_mul, abs_of_nonneg h2]
    exact mul_le_of_le_one_right h2 (Real.abs_sin_le_one _)

lemma fourierTensor_abs_le {d : ℕ} (ν : Fin d → ℕ) (x : Fin d → ℝ) :
    |fourierTensor ν x| ≤ Real.sqrt 2 ^ d := by
  unfold fourierTensor
  rw [Finset.abs_prod]
  calc ∏ k, |fourierAtom (ν k) (x k)| ≤ ∏ _k : Fin d, Real.sqrt 2 :=
        Finset.prod_le_prod₀ (fun k _ => abs_nonneg _) fun k _ => fourierAtom_abs_le _ _
    _ = Real.sqrt 2 ^ d := by simp

/-- **Assumption 1 for Fourier dictionaries** (blueprint `prop:fourier`). -/
theorem fourier_basis : FourierBasisStatement := by
  intro n J d idx x
  exact basisBound_of_abs_le (by positivity) fun j i => fourierTensor_abs_le _ _

end LargePrior
