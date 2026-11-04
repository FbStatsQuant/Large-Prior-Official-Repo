import LargePrior.SplineBook
import LargePrior.SplineReadout
import LargePrior.SplinePad

/-!
# Lemma bspline-profile (blueprint §S.4)
-/

open Finset

noncomputable section

namespace LargePrior

/-- Sup bound for a one-block approximant: `|s| ≤ |f₀| + error ≤ |R| + C⋆ · err`. -/
private lemma block_abs_le {d : ℕ} {f₀ s : (Fin d → ℝ) → ℝ} {R e : ℝ}
    (hR : ∀ x ∈ unitCube d, |f₀ x| ≤ R) (he : ∀ x ∈ unitCube d, |f₀ x - s x| ≤ e) :
    ∀ x ∈ unitCube d, |s x| ≤ |R| + e := by
  intro x hx
  have h1 := hR x hx
  have h2 := he x hx
  have h3 : |s x| ≤ |f₀ x| + |f₀ x - s x| := by
    have := abs_sub_abs_le_abs_sub (s x) (f₀ x)
    rw [abs_sub_comm] at this
    linarith
  linarith [le_abs_self R]

/-- **Lemma bspline-profile, parts 1 and 3.** -/
theorem bspline_profile : BSplineProfileStatement := by
  intro d q α Cstar Cdual R hq hα hCstar hCdual hread
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨(q : ℝ) ^ d, Cstar * ∑ k, (2 * q : ℝ) ^ α k,
    Cdual ^ d * (|R| + Cstar * d) + 1, by positivity, by positivity, by positivity, ?_⟩
  intro H f₀ m hR hOB hm
  set ℓ : Fin d → ℕ := fun k => splineLevel q (H k) (m k) with hℓdef
  have hℓH : ∀ k, ℓ k ≤ H k := fun k => splineLevel_le _ _ _
  have hbd := fun k => splineLevel_bounds hq (hm k).1 (hm k).2
  obtain ⟨θb, hθb⟩ := hOB ℓ
  -- the block error is at most `C⋆ d`
  have herr1 : Cstar * ∑ k, (splineDim q (ℓ k) : ℝ) ^ (-α k) ≤ Cstar * d := by
    apply mul_le_mul_of_nonneg_left _ hCstar
    calc ∑ k, (splineDim q (ℓ k) : ℝ) ^ (-α k) ≤ ∑ _k : Fin d, (1 : ℝ) :=
          Finset.sum_le_sum fun k _ =>
            rpow_neg_le_one_of_one_le (one_le_splineDim hq _) (hα k)
      _ = d := by simp
  have hcoef : ∀ j, |θb j| ≤ Cdual ^ d * (|R| + Cstar * d) := by
    intro j
    refine tensor_readout hq hCdual hread ℓ θb _ ?_ j
    intro x hx
    have := block_abs_le hR hθb x hx
    linarith
  refine ⟨padBlock ℓ θb, ?_, ?_, ?_⟩
  · refine (suppCard_padBlock_le ℓ θb).trans ?_
    calc ∏ k, (splineDim q (ℓ k) : ℝ) ≤ ∏ k, ((q : ℝ) * m k) :=
          Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => (hbd k).2)
      _ = (q : ℝ) ^ d * ∏ k, (m k : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro x hx
    rw [splineSeries_padBlock hℓH]
    refine (hθb x hx).trans ?_
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCstar
    calc ∑ k, (splineDim q (ℓ k) : ℝ) ^ (-α k)
        ≤ ∑ k, (2 * q : ℝ) ^ α k * (m k : ℝ) ^ (-α k) :=
          Finset.sum_le_sum fun k _ =>
            rpow_neg_le_of_level hq (hm k).1 (hα k) (hbd k).1
      _ ≤ ∑ k, (∑ i, (2 * q : ℝ) ^ α i) * (m k : ℝ) ^ (-α k) := by
          refine Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact Finset.single_le_sum (f := fun i => (2 * q : ℝ) ^ α i)
            (fun i _ => by positivity) (Finset.mem_univ k)
      _ = (∑ i, (2 * q : ℝ) ^ α i) * ∑ k, (m k : ℝ) ^ (-α k) := by
          rw [Finset.mul_sum]
  · intro ι
    refine abs_padBlock_le (by positivity) (fun j => (hcoef j).trans (by linarith)) ι

/-- **Lemma bspline-profile, part 2** (isotropic). -/
theorem bspline_profile_cube : BSplineProfileCubeStatement := by
  intro d q α Cstar Cdual R hd hq hα hCstar hCdual hread
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  refine ⟨(q : ℝ) ^ d, Cstar * (2 * q : ℝ) ^ α, Cdual ^ d * (|R| + Cstar) + 1,
    by positivity, by positivity, by positivity, ?_⟩
  intro H f₀ m hR hOB hm
  have hne : (Finset.univ : Finset (Fin d)).Nonempty := ⟨⟨0, hd⟩, Finset.mem_univ _⟩
  obtain ⟨k₀, -, hk₀⟩ := Finset.exists_mem_eq_inf' hne m
  set mm := Finset.univ.inf' hne m with hmm
  have hmm_le : ∀ k, mm ≤ m k := fun k => Finset.inf'_le _ (Finset.mem_univ k)
  have hmm1 : 1 ≤ mm := by rw [hk₀]; exact (hm k₀).1
  have hmmU : mm ≤ splineUnionDim q H := by rw [hk₀]; exact (hm k₀).2
  set ℓ₀ := splineLevel q H mm with hℓ₀
  have hbd := splineLevel_bounds hq hmm1 hmmU
  obtain ⟨θb, hθb⟩ := hOB ℓ₀
  have herr1 : Cstar * (splineDim q ℓ₀ : ℝ) ^ (-α) ≤ Cstar :=
    mul_le_of_le_one_right hCstar (rpow_neg_le_one_of_one_le (one_le_splineDim hq _) hα)
  have hcoef : ∀ j, |θb j| ≤ Cdual ^ d * (|R| + Cstar) := by
    intro j
    refine tensor_readout hq hCdual hread (fun _ => ℓ₀) θb _ ?_ j
    intro x hx
    have := block_abs_le hR hθb x hx
    linarith
  refine ⟨padBlock (H := fun _ => H) (fun _ => ℓ₀) θb, ?_, ?_, ?_⟩
  · refine (suppCard_padBlock_le _ θb).trans ?_
    calc ∏ _k : Fin d, (splineDim q ℓ₀ : ℝ) ≤ ∏ k, ((q : ℝ) * m k) := by
          refine Finset.prod_le_prod₀ (fun k _ => by positivity) (fun k _ => hbd.2.trans ?_)
          exact mul_le_mul_of_nonneg_left (by exact_mod_cast hmm_le k) (by positivity)
      _ = (q : ℝ) ^ d * ∏ k, (m k : ℝ) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  · intro x hx
    rw [splineSeries_padBlock (fun _ => splineLevel_le _ _ _)]
    refine (hθb x hx).trans ?_
    rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ hCstar
    calc (splineDim q ℓ₀ : ℝ) ^ (-α) ≤ (2 * q : ℝ) ^ α * (mm : ℝ) ^ (-α) :=
          rpow_neg_le_of_level hq hmm1 hα hbd.1
      _ ≤ (2 * q : ℝ) ^ α * ∑ k, (m k : ℝ) ^ (-α) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          rw [hk₀]
          exact Finset.single_le_sum (f := fun k => (m k : ℝ) ^ (-α))
            (fun k _ => by positivity) (Finset.mem_univ k₀)
  · intro ι
    refine abs_padBlock_le (by positivity) (fun j => (hcoef j).trans (by linarith)) ι

end LargePrior
