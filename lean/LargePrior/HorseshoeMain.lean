import LargePrior.Asymptotic
import LargePrior.HorseshoeAsymptotic

/-!
# Theorem 1 for the horseshoe prior
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

/-- **Theorem 1 for the horseshoe prior with a deterministic global scale.** -/
theorem main_horseshoe : MainHorseshoeStatement := by
  intro J X f₀ σ τ εt δ E M a K η μ'' cδ cτ B h
  have hHS := horseshoe_assumption3 J εt δ E τ a η μ'' cδ cτ B h.hJ h.hnεt h.hη h.hμ'' h.hcδ h.hcτ
    h.hB
    h.ha h.hεt h.hE h.hτ h.hcδev h.hτev h.hbudget
  have hA2 : ∀ᶠ n in atTop, ∃ θ₀ S, SparseApprox (X n) (f₀ n) (εt n) (δ n) (E n) (a n) θ₀ S ∧
      WG4 (horseshoePDF (τ n)) (J n) S η (εt n) 1 n := by
    filter_upwards [h.hA2, hHS] with n hn hHSn
    obtain ⟨θ₀, S, hSA⟩ := hn
    exact ⟨θ₀, S, hSA, hHSn.2.1 S hSA.2.2.2.1⟩
  exact asymptotic_theorem J X f₀ σ (fun n => horseshoePDF (τ n)) εt δ E M a K η (μ'' / 2) 1
    (B * (6 + 5 * B))
    { hσ := h.hσ, hK := h.hK, hη := h.hη, hη1 := h.hη1, hμ := half_pos h.hμ''
      hc4 := zero_le_one, hc5 := mul_nonneg h.hB (by linarith [h.hB])
      hJ := h.hJ, hnεt := h.hnεt, hs := h.hs, hM := h.hM
      hpdf := h.hτ.mono fun n hn => horseshoe_isProbDensity (τ n) hn
      hεt := h.hεt, hδ := h.hδ, hE := h.hE, ha := h.ha, hδεt := h.hδεt, hbasis := h.hbasis
      hA2 := hA2
      h3 := hHS.mono fun n hn => hn.1
      h5 := hHS.mono fun n hn => hn.2.2 }

end LargePrior
