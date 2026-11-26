import LargePrior.Posterior

/-!
# Lemma 3: prior mass of the sieve complement (`lem:sieve`)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

variable {J : ℕ}


private lemma prior_box {pdf : ℝ → ℝ} (hpdf : IsProbDensity pdf) (T : Finset (Fin J)) (δ : ℝ) :
    prior J pdf {θ | ∀ j ∈ T, δ < |θ j|} = (coordPrior pdf {t | δ < |t|}) ^ T.card := by
  have hset : {θ : Fin J → ℝ | ∀ j ∈ T, δ < |θ j|} =
      Set.pi Set.univ (fun j : Fin J => if j ∈ T then {t : ℝ | δ < |t|} else Set.univ) := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_pi, Set.mem_univ, true_implies]
    refine forall_congr' fun j => ?_
    by_cases hj : j ∈ T <;> simp [hj]
  have := isProbabilityMeasure_coordPrior hpdf
  rw [hset, prior, Measure.pi_pi]
  have h1 : ∀ j : Fin J, coordPrior pdf (if j ∈ T then {t : ℝ | δ < |t|} else Set.univ) =
      if j ∈ T then coordPrior pdf {t : ℝ | δ < |t|} else 1 := by
    intro j
    by_cases hj : j ∈ T <;> simp [hj]
  simp_rw [h1]
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

private lemma sieve_subset (δ : ℝ) (k : ℕ) :
    {θ : Fin J → ℝ | k ≤ numLarge δ θ} ⊆
      ⋃ T ∈ (univ : Finset (Fin J)).powersetCard k, {θ | ∀ j ∈ T, δ < |θ j|} := by
  intro θ hθ
  obtain ⟨T, hT, hc⟩ := Finset.exists_subset_card_eq (s := univ.filter (fun j => δ < |θ j|))
    (n := k) hθ
  simp only [Set.mem_iUnion]
  refine ⟨T, ?_, ?_⟩
  · simp [Finset.mem_powersetCard, hc]
  · intro j hj
    exact (Finset.mem_filter.1 (hT hj)).2

private lemma rpow_sieve (hJ : 1 ≤ J) {μ : ℝ} (k : ℕ) :
    ((J : ℝ) ^ k) * (((J : ℝ) ^ (-(1 + μ))) ^ k) = (J : ℝ) ^ (-(μ * k)) := by
  have hpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have h1 : (J : ℝ) * (J : ℝ) ^ (-(1 + μ)) = (J : ℝ) ^ (-μ) := by
    nth_rewrite 1 [← Real.rpow_one (J : ℝ)]
    rw [← Real.rpow_add hpos]
    congr 1
    ring
  rw [← mul_pow, h1, ← Real.rpow_mul_natCast hpos.le]
  congr 1
  ring

/-- **Lemma 3**: under (WG3), `Π{N_δ(θ) ≥ k} ≤ J^{−μk}` for every `k`. -/
theorem sieve_mass {pdf : ℝ → ℝ} (hpdf : IsProbDensity pdf) {δ μ : ℝ} (hJ : 1 ≤ J)
    (hμ : 0 < μ) (h3 : WG3 pdf δ μ J) (k : ℕ) :
    prior J pdf {θ | k ≤ numLarge δ θ} ≤ ENNReal.ofReal ((J : ℝ) ^ (-(μ * k))) := by
  have _ := hμ
  have hν : coordPrior pdf {t | δ < |t|} ^ k ≤ ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ))) ^ k :=
    pow_le_pow_left' h3 k
  have hch : ((J.choose k : ℕ) : ℝ≥0∞) ≤ ENNReal.ofReal ((J : ℝ) ^ k) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by exact_mod_cast Nat.choose_le_pow J k)
  calc prior J pdf {θ | k ≤ numLarge δ θ}
      ≤ prior J pdf (⋃ T ∈ (univ : Finset (Fin J)).powersetCard k, {θ | ∀ j ∈ T, δ < |θ j|}) :=
        measure_mono (sieve_subset δ k)
    _ ≤ ∑ T ∈ (univ : Finset (Fin J)).powersetCard k,
          prior J pdf {θ | ∀ j ∈ T, δ < |θ j|} := measure_biUnion_finset_le _ _
    _ = ∑ T ∈ (univ : Finset (Fin J)).powersetCard k, coordPrior pdf {t | δ < |t|} ^ k :=
        Finset.sum_congr rfl fun T hT => by
          rw [prior_box hpdf, (Finset.mem_powersetCard.1 hT).2]
    _ = (J.choose k : ℝ≥0∞) * coordPrior pdf {t | δ < |t|} ^ k := by
        rw [Finset.sum_const, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin,
          nsmul_eq_mul]
    _ ≤ ENNReal.ofReal ((J : ℝ) ^ k) * ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ))) ^ k :=
        mul_le_mul' hch hν
    _ = ENNReal.ofReal ((J : ℝ) ^ (-(μ * k))) := by
        rw [← ENNReal.ofReal_pow (Real.rpow_nonneg (Nat.cast_nonneg _) _),
          ← ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) _), rpow_sieve hJ]

/-- **Lemma 3**, exponential form: `Π(Θᶜ(m)) ≤ exp(−μ m log J)`. -/
theorem sieve_mass_exp {pdf : ℝ → ℝ} (hpdf : IsProbDensity pdf) {δ μ : ℝ} (hJ : 1 ≤ J)
    (hμ : 0 < μ) (h3 : WG3 pdf δ μ J) (m : ℕ) :
    prior J pdf (denseSet δ m) ≤ ENNReal.ofReal (Real.exp (-(μ * m * Real.log J))) := by
  have hpos : (0 : ℝ) < J := by exact_mod_cast hJ
  have h := sieve_mass hpdf hJ hμ h3 m
  have hsub : denseSet (J := J) δ m ⊆ {θ | m ≤ numLarge δ θ} := fun θ (hθ : m < numLarge δ θ) => (le_of_lt hθ : m ≤ numLarge δ θ)
  refine (measure_mono hsub).trans (h.trans (le_of_eq ?_))
  congr 1
  rw [Real.rpow_def_of_pos hpos]
  congr 1
  ring

end LargePrior
