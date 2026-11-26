import LargePrior.CorSpec

/-!
# Zero-padding a one-block spline into the multiresolution dictionary
-/

open Finset

noncomputable section

namespace LargePrior

/-- Zero-padding: place the block coefficients `θ` at the coordinates tagged by the levels `ℓ`,
and `0` at every other coordinate of `D_H^{(q)}`. -/
def padBlock {d q : ℕ} {H : Fin d → ℕ} (ℓ : Fin d → ℕ)
    (θ : ((k : Fin d) → Fin (splineDim q (ℓ k))) → ℝ) : SplineIdx q H → ℝ := fun ι =>
  if h : ∀ k, ((ι k).1 : ℕ) = ℓ k then
    θ (fun k => Fin.cast (congrArg (splineDim q) (h k)) (ι k).2)
  else 0

/-- The embedding of block indices into tagged indices of `D_H^{(q)}` (levels `ℓ`). -/
private def padEmb {d q : ℕ} {H : Fin d → ℕ} {ℓ : Fin d → ℕ} (hℓ : ∀ k, ℓ k ≤ H k)
    (j : (k : Fin d) → Fin (splineDim q (ℓ k))) : SplineIdx q H :=
  fun k => ⟨⟨ℓ k, Nat.lt_succ_of_le (hℓ k)⟩, j k⟩

private lemma padEmb_injective {d q : ℕ} {H : Fin d → ℕ} {ℓ : Fin d → ℕ}
    (hℓ : ∀ k, ℓ k ≤ H k) : Function.Injective (padEmb (q := q) (H := H) hℓ) := by
  intro j j' h
  funext k
  have hk := congrFun h k
  simp only [padEmb, Sigma.mk.inj_iff, true_and] at hk
  exact eq_of_heq hk

private lemma sigma_eq_of_fst {q n m : ℕ} (hm : m < n + 1)
    (s : Σ l : Fin (n + 1), Fin (splineDim q l)) (h : (s.1 : ℕ) = m) :
    (⟨⟨m, hm⟩, Fin.cast (congrArg (splineDim q) h) s.2⟩ :
      Σ l : Fin (n + 1), Fin (splineDim q l)) = s := by
  obtain ⟨⟨a, ha⟩, b⟩ := s
  subst h
  rfl

private lemma padBlock_padEmb {d q : ℕ} {H : Fin d → ℕ} {ℓ : Fin d → ℕ} (hℓ : ∀ k, ℓ k ≤ H k)
    (θ : ((k : Fin d) → Fin (splineDim q (ℓ k))) → ℝ) (j : (k : Fin d) → Fin (splineDim q (ℓ k))) :
    padBlock (H := H) ℓ θ (padEmb hℓ j) = θ j := by
  have h : ∀ k, (((padEmb (H := H) hℓ j) k).1 : ℕ) = ℓ k := fun k => rfl
  rw [padBlock, dite_eq_left h]
  rfl

private lemma padBlock_eq_zero {d q : ℕ} {H : Fin d → ℕ} {ℓ : Fin d → ℕ}
    (θ : ((k : Fin d) → Fin (splineDim q (ℓ k))) → ℝ) (ι : SplineIdx q H)
    (h : ¬ ∀ k, ((ι k).1 : ℕ) = ℓ k) : padBlock ℓ θ ι = 0 := by
  rw [padBlock, dite_eq_right h]

/-- Every tagged index at the levels `ℓ` is in the image of `padEmb`. -/
private lemma mem_image_padEmb {d q : ℕ} {H : Fin d → ℕ} {ℓ : Fin d → ℕ} (hℓ : ∀ k, ℓ k ≤ H k)
    (ι : SplineIdx q H) (h : ∀ k, ((ι k).1 : ℕ) = ℓ k) :
    ι ∈ univ.image (padEmb hℓ) := by
  refine mem_image.2 ⟨fun k => Fin.cast (congrArg (splineDim q) (h k)) (ι k).2, mem_univ _, ?_⟩
  funext k
  exact sigma_eq_of_fst _ (ι k) (h k)

/-- Padding does not change the represented function (when every `ℓ_k ≤ H_k`). -/
lemma splineSeries_padBlock {d q : ℕ} {H : Fin d → ℕ} {ℓ : Fin d → ℕ} (hℓ : ∀ k, ℓ k ≤ H k)
    (θ : ((k : Fin d) → Fin (splineDim q (ℓ k))) → ℝ) (x : Fin d → ℝ) :
    splineSeries (padBlock (H := H) ℓ θ) x = blockSeries q ℓ θ x := by
  unfold splineSeries blockSeries
  symm
  calc ∑ j, θ j * ∏ k, bspline q (2 ^ ℓ k) (j k : ℕ) (x k)
      = ∑ j, padBlock (H := H) ℓ θ (padEmb hℓ j) * splineAtom (padEmb hℓ j) x := by
        refine sum_congr rfl fun j _ => ?_
        rw [padBlock_padEmb]
        rfl
    _ = ∑ ι ∈ univ.image (padEmb hℓ), padBlock (H := H) ℓ θ ι * splineAtom ι x :=
        (sum_image (f := fun ι => padBlock (H := H) ℓ θ ι * splineAtom ι x)
          fun a _ b _ hab => padEmb_injective hℓ hab).symm
    _ = ∑ ι, padBlock (H := H) ℓ θ ι * splineAtom ι x := by
        refine sum_subset (subset_univ _) fun ι _ hι => ?_
        rw [padBlock_eq_zero θ ι fun h => hι (mem_image_padEmb hℓ ι h), zero_mul]

/-- The padded vector has at most `∏_k D_{ℓ_k}` nonzero coordinates. -/
lemma suppCard_padBlock_le {d q : ℕ} {H : Fin d → ℕ} (ℓ : Fin d → ℕ)
    (θ : ((k : Fin d) → Fin (splineDim q (ℓ k))) → ℝ) :
    (suppCard (padBlock (H := H) ℓ θ) : ℝ) ≤ ∏ k, (splineDim q (ℓ k) : ℝ) := by
  have hcard : suppCard (padBlock (H := H) ℓ θ) ≤ ∏ k, splineDim q (ℓ k) := by
    by_cases hℓ : ∀ k, ℓ k ≤ H k
    · calc suppCard (padBlock (H := H) ℓ θ)
          ≤ (univ.image (padEmb (H := H) hℓ)).card := by
            refine card_le_card fun ι hι => ?_
            refine mem_image_padEmb hℓ ι ?_
            by_contra h
            exact (mem_filter.1 hι).2 (padBlock_eq_zero θ ι h)
        _ ≤ (univ : Finset ((k : Fin d) → Fin (splineDim q (ℓ k)))).card := card_image_le
        _ = ∏ k, splineDim q (ℓ k) := by
            rw [card_univ, Fintype.card_pi]
            simp only [Fintype.card_fin]
    · have hempty : univ.filter (fun ι => padBlock (H := H) ℓ θ ι ≠ 0) = ∅ := by
        refine filter_eq_empty_iff.2 fun ι _ => ?_
        rw [not_not]
        refine padBlock_eq_zero θ ι fun h => hℓ fun k => ?_
        rw [← h k]
        exact Nat.lt_succ_iff.1 (ι k).1.isLt
      rw [suppCard, hempty, card_empty]
      exact Nat.zero_le _
  exact_mod_cast hcard

/-- Padding preserves coefficient bounds. -/
lemma abs_padBlock_le {d q : ℕ} {H : Fin d → ℕ} {ℓ : Fin d → ℕ}
    {θ : ((k : Fin d) → Fin (splineDim q (ℓ k))) → ℝ} {E : ℝ} (hE : 0 ≤ E)
    (hθ : ∀ j, |θ j| ≤ E) (ι : SplineIdx q H) : |padBlock ℓ θ ι| ≤ E := by
  by_cases h : ∀ k, ((ι k).1 : ℕ) = ℓ k
  · rw [padBlock, dite_eq_left h]
    exact hθ _
  · rw [padBlock_eq_zero θ ι h, abs_zero]
    exact hE

end LargePrior
