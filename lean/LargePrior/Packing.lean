import LargePrior.Basic

/-!
# Lemma 6: packing bound in a finite-dimensional inner product space (blueprint `lem:packing`)
-/

open MeasureTheory Metric
open scoped ENNReal NNReal Topology

noncomputable section

namespace LargePrior

/-- **Lemma 6(a)**: an `r`-separated finite subset of a ball of radius `R` in a `k`-dimensional
inner product space has at most `(1 + 2R/r)^k` points. -/
theorem packing_card_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x : E) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (G : Finset E)
    (hG : ∀ g ∈ G, dist g x ≤ R) (hsep : ∀ g ∈ G, ∀ g' ∈ G, g ≠ g' → r < dist g g') :
    (G.card : ℝ) ≤ (1 + 2 * R / r) ^ Module.finrank ℝ E := by
  classical
  borelize E
  let μ : Measure E := Measure.addHaar
  set k := Module.finrank ℝ E
  have hr2 : 0 < r / 2 := by positivity
  have hρ : 0 < R + r / 2 := by positivity
  have D : Set.Pairwise (G : Set E) (Function.onFun Disjoint fun c => ball (c : E) (r / 2)) := by
    intro c hc d hd hcd
    apply ball_disjoint_ball
    have := hsep c hc d hd hcd
    linarith
  have A_subset : (⋃ c ∈ G, ball (c : E) (r / 2)) ⊆ ball x (R + r / 2) := by
    refine Set.iUnion₂_subset fun c hc => ?_
    apply ball_subset_ball'
    have := hG c hc
    linarith
  have I : (G.card : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ k) * μ (ball 0 1) ≤
      ENNReal.ofReal ((R + r / 2) ^ k) * μ (ball 0 1) := by
    calc (G.card : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ k) * μ (ball 0 1)
        = μ (⋃ c ∈ G, ball (c : E) (r / 2)) := by
          rw [measure_biUnion_finset D fun c _ => measurableSet_ball]
          simp only [μ.addHaar_ball_of_pos _ hr2, Finset.sum_const, nsmul_eq_mul, mul_assoc, k]
      _ ≤ μ (ball x (R + r / 2)) := measure_mono A_subset
      _ = _ := μ.addHaar_ball_of_pos _ hρ
  have J : (G.card : ℝ≥0∞) * ENNReal.ofReal ((r / 2) ^ k) ≤ ENNReal.ofReal ((R + r / 2) ^ k) :=
    (ENNReal.mul_le_mul_iff_left (measure_ball_pos _ _ zero_lt_one).ne' measure_ball_lt_top.ne).1 I
  have K : (G.card : ℝ) * (r / 2) ^ k ≤ (R + r / 2) ^ k := by
    have := ENNReal.toReal_le_of_le_ofReal (pow_nonneg hρ.le _) J
    simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hr2.le _)] using this
  have hpow : (1 + 2 * R / r) ^ k = (R + r / 2) ^ k / (r / 2) ^ k := by
    rw [← div_pow]
    congr 1
    field_simp
    ring
  rw [hpow, le_div_iff₀ (pow_pos hr2 _)]
  exact K

/-- **Lemma 6(b)**: every subset of a ball of radius `R` has a finite `r`-net inside it with at
most `(1 + 2R/r)^k` points. -/
theorem exists_net {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (x : E) {R r : ℝ} (hR : 0 < R) (hr : 0 < r) (F : Set E)
    (hF : ∀ z ∈ F, dist z x ≤ R) :
    ∃ G : Finset E, (↑G : Set E) ⊆ F ∧ (G.card : ℝ) ≤ (1 + 2 * R / r) ^ Module.finrank ℝ E ∧
      ∀ z ∈ F, ∃ g ∈ G, dist z g ≤ r := by
  classical
  set B : ℝ := (1 + 2 * R / r) ^ Module.finrank ℝ E
  let P : ℕ → Prop := fun n => ∃ G : Finset E, (↑G : Set E) ⊆ F ∧
    (∀ g ∈ G, ∀ g' ∈ G, g ≠ g' → r < dist g g') ∧ G.card = n
  have hbound : ∀ n, P n → n ≤ ⌊B⌋₊ := by
    rintro n ⟨G, hGF, hGs, rfl⟩
    exact Nat.le_floor (packing_card_le x hR hr G (fun g hg => hF g (hGF hg)) hGs)
  have hP0 : P 0 := ⟨∅, by simp, by simp, rfl⟩
  obtain ⟨G, hGF, hGs, hGc⟩ := Nat.findGreatest_spec (P := P) (Nat.zero_le _) hP0
  refine ⟨G, hGF, packing_card_le x hR hr G (fun g hg => hF g (hGF hg)) hGs, ?_⟩
  intro z hz
  by_contra hcon
  push Not at hcon
  have hzG : z ∉ G := fun h => by
    have := hcon z h
    rw [dist_self] at this
    linarith
  have hPn : P (Nat.findGreatest P ⌊B⌋₊ + 1) := by
    refine ⟨insert z G, ?_, ?_, ?_⟩
    · simpa [Set.insert_subset_iff] using ⟨hz, hGF⟩
    · intro g hg g' hg' hne
      rw [Finset.mem_insert] at hg hg'
      rcases hg with rfl | hg <;> rcases hg' with rfl | hg'
      · exact absurd rfl hne
      · exact hcon g' hg'
      · rw [dist_comm]; exact hcon g hg
      · exact hGs g hg g' hg' hne
    · rw [Finset.card_insert_of_notMem hzG, hGc]
  have h1 := Nat.le_findGreatest (hbound _ hPn) hPn
  omega

end LargePrior
