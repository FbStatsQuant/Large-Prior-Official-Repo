import LargePrior.Horseshoe

/-!
# (WG3)–(WG5) at a fixed sample size (blueprint Part P, fixed `n`)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology

noncomputable section

namespace LargePrior

/-- (WG3) from a tail bound at a smaller threshold (blueprint `lem:wg3-of-tail`). -/
lemma wg3_of_tail {pdf : ℝ → ℝ} {δ μ u : ℝ} {J : ℕ} (huδ : u ≤ δ)
    (htail : coordPrior pdf {t | u < |t|} ≤ ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ)))) :
    WG3 pdf δ μ J :=
  le_trans (measure_mono fun _ (ht : δ < |_|) => lt_of_le_of_lt huδ ht) htail

/-- (WG4) for every active set, from a tail bound at `η ε̃ / J` (blueprint `lem:wg4-of-tail`). -/
lemma wg4_of_tail {pdf : ℝ → ℝ} (hpdf : IsProbDensity pdf) {J : ℕ} (hJ : 2 ≤ J)
    {μ η εt c4 : ℝ} {n : ℕ} (hμ : 0 < μ) (hJμ : 2 ≤ (J : ℝ) ^ μ) (hη : 0 < η) (hεt : 0 < εt)
    (hc4 : Real.log 2 ≤ c4 * n * εt ^ 2)
    (htail : coordPrior pdf {t | η * εt / J < |t|} ≤ ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ))))
    (S : Finset (Fin J)) :
    WG4 pdf J S η εt c4 n := by
  -- `0 < μ` is implied by `2 ≤ J ^ μ` here and is not needed.
  have _ := hμ
  have := isProbabilityMeasure_coordPrior hpdf
  have := isProbabilityMeasure_prior hpdf J
  have hJpos : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  set u : ℝ := η * εt / J with hu
  have hu0 : 0 ≤ u := by positivity
  set G : Set (Fin J → ℝ) := {θ | ∀ j ∈ Sᶜ, |θ j| ≤ u} with hG
  -- G is inside the event
  have hGsub : G ⊆ {θ | ∑ j ∈ Sᶜ, |θ j| ≤ η * εt} := by
    intro θ hθ
    have h1 : ∑ j ∈ Sᶜ, |θ j| ≤ ∑ _j ∈ Sᶜ, u := Finset.sum_le_sum hθ
    have h2 : ((Sᶜ).card : ℝ) ≤ J := by
      exact_mod_cast (Finset.card_le_univ _).trans (Fintype.card_fin J).le
    have h3 : ((Sᶜ).card : ℝ) * u ≤ J * u := mul_le_mul_of_nonneg_right h2 hu0
    have h4 : (J : ℝ) * u = η * εt := by rw [hu]; field_simp
    simp only [Finset.sum_const, nsmul_eq_mul] at h1
    show ∑ j ∈ Sᶜ, |θ j| ≤ η * εt
    linarith
  -- complement is a finite union of coordinate tails
  have hGc : Gᶜ ⊆ ⋃ j ∈ Sᶜ, Function.eval j ⁻¹' {t : ℝ | u < |t|} := by
    intro θ hθ
    simp only [hG, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall, not_le] at hθ
    obtain ⟨j, hj, hlt⟩ := hθ
    exact Set.mem_biUnion hj hlt
  have hmeas : MeasurableSet {t : ℝ | u < |t|} :=
    measurableSet_lt measurable_const measurable_abs
  have hcyl : ∀ j, prior J pdf (Function.eval j ⁻¹' {t : ℝ | u < |t|}) =
      coordPrior pdf {t : ℝ | u < |t|} := fun j =>
    (measurePreserving_eval (fun _ : Fin J => coordPrior pdf) j).measure_preimage
      hmeas.nullMeasurableSet
  have hGc_le : prior J pdf Gᶜ ≤ ENNReal.ofReal ((J : ℝ) ^ (-μ)) := by
    calc prior J pdf Gᶜ
        ≤ prior J pdf (⋃ j ∈ Sᶜ, Function.eval j ⁻¹' {t : ℝ | u < |t|}) := measure_mono hGc
      _ ≤ ∑ j ∈ Sᶜ, prior J pdf (Function.eval j ⁻¹' {t : ℝ | u < |t|}) :=
          measure_biUnion_finset_le _ _
      _ = ∑ _j ∈ Sᶜ, coordPrior pdf {t : ℝ | u < |t|} := by simp only [hcyl]
      _ ≤ ∑ _j ∈ Sᶜ, ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ))) := by
          exact Finset.sum_le_sum fun _ _ => htail
      _ = ((Sᶜ).card : ℝ≥0∞) * ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ))) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (J : ℝ≥0∞) * ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ))) := by
          gcongr
          exact_mod_cast (Finset.card_le_univ _).trans (Fintype.card_fin J).le
      _ = ENNReal.ofReal ((J : ℝ) ^ (-μ)) := by
          rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
          congr 1
          rw [show -(1 + μ) = -μ + (-1 : ℝ) by ring, Real.rpow_add hJpos, Real.rpow_neg_one]
          field_simp
  have hJmu : (J : ℝ) ^ (-μ) ≤ 1 / 2 := by
    rw [Real.rpow_neg hJpos.le]
    rw [inv_le_comm₀ (by positivity) (by norm_num)]
    linarith
  have hexp : Real.exp (-(c4 * n * εt ^ 2)) ≤ 1 / 2 := by
    calc Real.exp (-(c4 * n * εt ^ 2)) ≤ Real.exp (-Real.log 2) :=
          Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hhalf : ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) = 1 := by
    rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]; norm_num
  have hGlow : ENNReal.ofReal (1 / 2) ≤ prior J pdf G := by
    have h1 : (1 : ℝ≥0∞) ≤ prior J pdf G + prior J pdf Gᶜ := by
      calc (1 : ℝ≥0∞) = prior J pdf (G ∪ Gᶜ) := by rw [Set.union_compl_self, measure_univ]
        _ ≤ prior J pdf G + prior J pdf Gᶜ := measure_union_le _ _
    have h2 : prior J pdf Gᶜ ≤ ENNReal.ofReal (1 / 2) :=
      hGc_le.trans (ENNReal.ofReal_le_ofReal hJmu)
    have h3 : ENNReal.ofReal (1 / 2) + ENNReal.ofReal (1 / 2) ≤
        prior J pdf G + ENNReal.ofReal (1 / 2) := by
      rw [hhalf]; exact h1.trans (add_le_add le_rfl h2)
    exact (ENNReal.add_le_add_iff_right ENNReal.ofReal_ne_top).mp h3
  exact (ENNReal.ofReal_le_ofReal hexp).trans (hGlow.trans (measure_mono hGsub))

/-- (WG5) for the horseshoe with `π_low = c_HS τ / max(E, τ)²` (blueprint `lem:wg5-hs`). -/
lemma horseshoe_wg5 {τ E εt c5 : ℝ} {a n : ℕ} (hτ : 0 < τ) (hE : 0 < E)
    (hbudget : (a : ℝ) * max 0 (Real.log a + 2 * Real.log (1 / εt) -
        Real.log (hsConst * τ / max E τ ^ 2)) ≤ c5 * n * εt ^ 2) :
    WG5 (horseshoePDF τ) E εt c5 a n := by
  refine ⟨hsConst * τ / max E τ ^ 2, ?_, ?_, hbudget⟩
  · exact div_pos (mul_pos (lt_of_lt_of_le (by norm_num) hsConst_ge) hτ)
      (pow_pos (lt_max_of_lt_left hE) 2)
  · have h0 : ∀ᵐ t ∂(volume : Measure ℝ), t ≠ 0 := by
      rw [ae_iff]
      simp
    filter_upwards [h0] with t ht htE
    exact horseshoe_lower hτ hE ht htE

end LargePrior
