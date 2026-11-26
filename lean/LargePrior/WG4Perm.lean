import LargePrior.Spec

/-!
# (WG4) depends on the active set only through its size

The coefficient prior is an iid product, so permuting coordinates preserves it. Hence the
probability in (WG4), `Π(∑_{j∉S} |θ_j| ≤ η ε̃)`, is the same for all sets `S` of a given size.
This is the remark in Assumption 3 of the paper ("the probability in (WG4) depends only on
`J_n − a_n`"), and it lets Corollary 1 assume (WG4) for one set of size `a_n` only.
-/

open MeasureTheory Finset

noncomputable section

namespace LargePrior

/-- A permutation of `Fin J` mapping `S'` onto `S` exists when `|S'| = |S|`. -/
lemma exists_perm_mem_iff {J : ℕ} {S S' : Finset (Fin J)} (hcard : S.card = S'.card) :
    ∃ σ : Equiv.Perm (Fin J), ∀ i, i ∈ S' ↔ σ i ∈ S := by
  classical
  have hc : Fintype.card {x // x ∈ S'} = Fintype.card {x // x ∈ S} := by
    simp only [Fintype.card_coe, hcard]
  have hc' : Fintype.card {x // x ∉ S'} = Fintype.card {x // x ∉ S} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, Fintype.card_coe,
      Fintype.card_coe, hcard]
  refine ⟨Equiv.subtypeCongr (Fintype.equivOfCardEq hc) (Fintype.equivOfCardEq hc'),
    fun i => ?_⟩
  by_cases h : i ∈ S'
  · have : Equiv.subtypeCongr (Fintype.equivOfCardEq hc) (Fintype.equivOfCardEq hc') i =
        (Fintype.equivOfCardEq hc ⟨i, h⟩ : Fin J) := by
      simp [Equiv.subtypeCongr, h]
    rw [this]
    exact ⟨fun _ => (Fintype.equivOfCardEq hc ⟨i, h⟩).2, fun _ => h⟩
  · have : Equiv.subtypeCongr (Fintype.equivOfCardEq hc) (Fintype.equivOfCardEq hc') i =
        (Fintype.equivOfCardEq hc' ⟨i, h⟩ : Fin J) := by
      simp [Equiv.subtypeCongr, h]
    rw [this]
    exact ⟨fun h' => absurd h' h, fun h' => absurd h' (Fintype.equivOfCardEq hc' ⟨i, h⟩).2⟩

/-- **(WG4) is invariant under the choice of the active set of a given size.** If (WG4) holds
for `S`, it holds for every `S'` with `|S'| = |S|`. -/
theorem wg4_of_card_eq {pdf : ℝ → ℝ} {J : ℕ} {S S' : Finset (Fin J)} (hcard : S.card = S'.card)
    {η εt c4 : ℝ} {n : ℕ} (h : WG4 pdf J S η εt c4 n) : WG4 pdf J S' η εt c4 n := by
  classical
  obtain ⟨σ, hσ⟩ := exists_perm_mem_iff hcard
  -- `T θ = θ ∘ σ⁻¹` preserves the iid product prior
  set T := MeasurableEquiv.piCongrLeft (fun _ : Fin J => ℝ) σ with hT
  have : SigmaFinite (coordPrior pdf) := by unfold coordPrior; infer_instance
  have hpres : MeasurePreserving T (prior J pdf) (prior J pdf) :=
    measurePreserving_piCongrLeft (fun _ : Fin J => coordPrior pdf) σ
  -- the (WG4) event for `S'` is the preimage of the event for `S`
  have hpre : T ⁻¹' {θ : Fin J → ℝ | ∑ j ∈ Sᶜ, |θ j| ≤ η * εt} =
      {θ | ∑ j ∈ S'ᶜ, |θ j| ≤ η * εt} := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_ofPred_eq]
    have hsum : ∑ j ∈ Sᶜ, |T θ j| = ∑ i ∈ S'ᶜ, |θ i| := by
      refine (Finset.sum_equiv σ (fun i => ?_) (fun i _ => ?_)).symm
      · simp only [Finset.mem_compl, hσ i]
      · rw [hT, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rw [hsum]
  unfold WG4 at h ⊢
  rw [← hpre, hpres.measure_preimage_equiv]
  exact h

end LargePrior
