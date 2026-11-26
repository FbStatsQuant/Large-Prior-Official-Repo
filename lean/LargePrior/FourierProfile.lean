import LargePrior.FourierExpand

/-!
# Lemma fourier-profile (`lem:fourier-profile`)
-/

open MeasureTheory Finset
open scoped Real

noncomputable section

namespace LargePrior

/-- **Lemma fourier-profile.** -/
theorem fourier_profile : FourierProfileStatement := by
  intro d α r CJ hα _hr hJ
  refine ⟨3 ^ d * ∑ k, jackC' (α k) (CJ k), ?_, ?_⟩
  · refine mul_nonneg (by positivity) (Finset.sum_nonneg fun k _ => ?_)
    unfold jackC'
    exact le_trans (by positivity) (le_max_right _ _)
  intro R f₀ M m hball hm
  obtain ⟨hcont, -, A, B, hA0, hB0, hAB, hAf, -⟩ := id hball
  obtain ⟨θ, hsupp, hθ, hP⟩ := Pop_expansion hcont hAf M m hm
  refine ⟨θ, hsupp.trans ?_, fun x => ?_, fun ν => (hθ ν).trans (by linarith)⟩
  · exact Finset.prod_le_prod₀ (fun k _ => by positivity)
      (fun k _ => by exact_mod_cast budgetAtoms_le (hm k).1)
  · rw [← hP x]
    exact Pop_error hα hJ hball (fun k => (hm k).1) x

end LargePrior
