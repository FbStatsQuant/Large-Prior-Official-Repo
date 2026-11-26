import LargePrior.ChebSpec
import LargePrior.Basis

/-!
# The Chebyshev fold and dictionary bound

The fold onto `[0,1]` turns each Chebyshev atom into the Fourier cosine atom of
the same frequency. The pointwise atom bound gives Assumption 1 on the unit cube.
-/

noncomputable section

namespace LargePrior

/-- The range of the fold is contained in the unit interval. -/
lemma chebFold_mem_Icc (u : ℝ) : chebFold u ∈ Set.Icc (0 : ℝ) 1 := by
  unfold chebFold
  constructor
  · linarith [Real.neg_one_le_cos (2 * Real.pi * u)]
  · linarith [Real.cos_le_one (2 * Real.pi * u)]

/-- Each point in the unit interval has a preimage in the first half-period. -/
lemma chebFold_surj (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    ∃ u ∈ Set.Icc (0 : ℝ) (1 / 2), chebFold u = x := by
  -- We use the inverse cosine to give an explicit preimage.
  -- Its range in [0, π] places this preimage in the requested half-period.
  have hπ : 0 < 2 * Real.pi := by positivity
  have hangle : Real.cos (Real.arccos (2 * x - 1)) = 2 * x - 1 :=
    Real.cos_arccos (by linarith [hx.1]) (by linarith [hx.2])
  refine ⟨Real.arccos (2 * x - 1) / (2 * Real.pi), ⟨?_, ?_⟩, ?_⟩
  · exact div_nonneg (Real.arccos_nonneg _) hπ.le
  · apply (div_le_iff₀ hπ).2
    linarith [Real.arccos_le_pi (2 * x - 1)]
  · unfold chebFold
    rw [mul_div_cancel₀ _ hπ.ne', hangle]
    ring

/-- Reflection about the origin preserves the fold. -/
lemma chebFold_even : Function.Even chebFold := by
  intro u
  simp only [chebFold, mul_neg, Real.cos_neg]

/-- Translation by one preserves the fold. -/
lemma chebFold_periodic : Function.Periodic chebFold 1 := by
  intro u
  simp only [chebFold, mul_add, mul_one, Real.cos_add_two_pi]

/-- The fold is continuous on the whole real line. -/
lemma chebFold_continuous : Continuous chebFold := by
  unfold chebFold
  fun_prop

/-- The fold increases distances by at most a factor of π. -/
lemma chebFold_lipschitz (u v : ℝ) : |chebFold u - chebFold v| ≤ Real.pi * |u - v| := by
  -- Apply the cosine Lipschitz bound directly to the fold.
  -- The factor 2π in the argument and the outer division by 2 give π.
  calc
    |chebFold u - chebFold v| =
        |Real.cos (2 * Real.pi * u) - Real.cos (2 * Real.pi * v)| / 2 := by
      unfold chebFold
      rw [← sub_div, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      exact congrArg (fun t : ℝ => |t| / 2) (by ring)
    _ ≤ |2 * Real.pi * u - 2 * Real.pi * v| / 2 :=
      div_le_div_of_nonneg_right (Real.abs_cos_sub_cos_le _ _) (by norm_num)
    _ = Real.pi * |u - v| := by
      rw [← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi)]
      ring

/-- Folding turns a Chebyshev atom into the corresponding Fourier atom, including degree zero. -/
lemma chebAtom_chebFold (j : ℕ) (u : ℝ) :
    chebAtom j (chebFold u) = fourierAtom (if j = 0 then 0 else 2 * j - 1) u := by
  by_cases hj : j = 0
  · simp [hj, chebAtom, fourierAtom]
  have hshift : 2 * chebFold u - 1 = Real.cos (2 * Real.pi * u) := by
    unfold chebFold
    ring
  have hfreq : 2 * j - 1 ≠ 0 := by omega
  have hodd : (2 * j - 1) % 2 = 1 := by omega
  have hhalf : (2 * j - 1 + 1) / 2 = j := by omega
  rw [ite_eq_right hj, chebAtom, ite_eq_right hj, hshift, Polynomial.Chebyshev.T_real_cos,
    Int.cast_natCast, fourierAtom, ite_eq_right hfreq, ite_eq_left hodd, hhalf]
  rw [show (j : ℝ) * (2 * Real.pi * u) = 2 * Real.pi * j * u by ring]

/-- Folding every coordinate gives the tensor product of the corresponding Fourier atoms. -/
lemma chebTensor_fold {d : ℕ} (j : Fin d → ℕ) (u : Fin d → ℝ) :
    chebTensor j (fun k => chebFold (u k)) =
      fourierTensor (fun k => if j k = 0 then 0 else 2 * j k - 1) u := by
  unfold chebTensor fourierTensor
  exact Finset.prod_congr rfl fun k _ => chebAtom_chebFold (j k) (u k)

/-- Every Chebyshev atom is bounded in absolute value by √2 on the unit interval. -/
lemma chebAtom_abs_le (j : ℕ) (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    |chebAtom j x| ≤ Real.sqrt 2 := by
  by_cases hj : j = 0
  · norm_num [chebAtom, hj]
  have hx' : |2 * x - 1| ≤ 1 :=
    abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
  rw [chebAtom, ite_eq_right hj, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2)]
  exact mul_le_of_le_one_right (Real.sqrt_nonneg 2)
    (Polynomial.Chebyshev.abs_eval_T_real_le_one (j : ℤ) hx')

/-- **Assumption 1 for Chebyshev dictionaries** with `K = (√2)^d`. -/
theorem chebyshev_basis : ChebyshevBasisStatement := by
  intro n J d idx x hx
  apply basisBound_of_abs_le (by positivity)
  intro j i
  rw [chebTensor, Finset.abs_prod]
  calc
    ∏ k, |chebAtom (idx j k) (x i k)| ≤ ∏ _k : Fin d, Real.sqrt 2 :=
      Finset.prod_le_prod₀ (fun _ _ => abs_nonneg _) fun k _ =>
        chebAtom_abs_le (idx j k) (x i k) (hx i k)
    _ = Real.sqrt 2 ^ d := by simp

end LargePrior
