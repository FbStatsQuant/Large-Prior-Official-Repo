import LargePrior.CorSpec

/-!
# Tensor coefficient readout (`eq:dual-readout`)

The univariate stability `BSplineReadout q C_dual` gives, one coordinate at a time, the tensor
bound `|θ_j| ≤ C_dual^d · sup_{[0,1]^d} |s|` for a one-block tensor spline `s`.
-/

open Finset

noncomputable section

namespace LargePrior

/-- Splitting off the first coordinate of a one-block tensor spline:
`s(x) = ∑_{j₀} c_{j₀}(x') B_{ℓ₀,j₀}(x₀)` with `c_{j₀}` the `d`-variate block series with
coefficients `θ(cons j₀ ·)` evaluated at `x' = tail x`. -/
private lemma blockSeries_succ {d : ℕ} (q : ℕ) (ℓ : Fin (d + 1) → ℕ)
    (θ : ((k : Fin (d + 1)) → Fin (splineDim q (ℓ k))) → ℝ) (x : Fin (d + 1) → ℝ) :
    blockSeries q ℓ θ x =
      ∑ j₀ : Fin (splineDim q (ℓ 0)),
        blockSeries q (Fin.tail ℓ)
          (fun j' => θ (Fin.cons j₀ j' : (k : Fin (d + 1)) → Fin (splineDim q (ℓ k))))
          (Fin.tail x) * bspline q (2 ^ ℓ 0) (j₀ : ℕ) (x 0) := by
  unfold blockSeries
  rw [← (Fin.consEquiv fun k : Fin (d + 1) => Fin (splineDim q (ℓ k))).sum_comp,
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j₀ _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j' _ => ?_
  have hc : (Fin.consEquiv fun k : Fin (d + 1) => Fin (splineDim q (ℓ k))) (j₀, j') =
      (Fin.cons j₀ j' : (k : Fin (d + 1)) → Fin (splineDim q (ℓ k))) := rfl
  simp only [hc, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ, Fin.tail]
  ring

/-- **Tensor readout** (`eq:dual-readout`): if `|∑_j θ_j ∏_k B_{ℓ_k,j_k}(x_k)| ≤ S` on `[0,1]^d`, then
`|θ_j| ≤ C_dual^d S` for every `j`. -/
lemma tensor_readout {d q : ℕ} {Cdual : ℝ} (hq : 1 ≤ q) (hC : 1 ≤ Cdual)
    (hR : BSplineReadout q Cdual) (ℓ : Fin d → ℕ)
    (θ : ((k : Fin d) → Fin (splineDim q (ℓ k))) → ℝ) (S : ℝ)
    (hS : ∀ x ∈ unitCube d, |blockSeries q ℓ θ x| ≤ S) (j : (k : Fin d) → Fin (splineDim q (ℓ k))) :
    |θ j| ≤ Cdual ^ d * S := by
  have _ := hq
  have _ := hC
  induction d generalizing S with
  | zero =>
    have hx : (Fin.elim0 : Fin 0 → ℝ) ∈ unitCube 0 := fun k => k.elim0
    have h0 := hS _ hx
    have hsum : blockSeries q ℓ θ Fin.elim0 = θ j := by
      unfold blockSeries
      rw [Fintype.sum_unique]
      simp only [Finset.univ_eq_empty, Finset.prod_empty, mul_one]
      congr 1
      exact Subsingleton.elim _ _
    rw [hsum] at h0
    simpa using h0
  | succ d ih =>
    -- coefficient bound for each first index, uniformly on the cube in the remaining coordinates
    have hc : ∀ j₀ : Fin (splineDim q (ℓ 0)), ∀ x' ∈ unitCube d,
        |blockSeries q (Fin.tail ℓ)
          (fun j' => θ (Fin.cons j₀ j' : (k : Fin (d + 1)) → Fin (splineDim q (ℓ k)))) x'|
          ≤ Cdual * S := by
      intro j₀ x' hx'
      refine hR (ℓ 0) (fun i => blockSeries q (Fin.tail ℓ)
          (fun j' => θ (Fin.cons i j' : (k : Fin (d + 1)) → Fin (splineDim q (ℓ k)))) x') S
        ?_ j₀
      intro t ht
      have hmem : (Fin.cons t x' : Fin (d + 1) → ℝ) ∈ unitCube (d + 1) := by
        intro k
        refine Fin.cases ?_ (fun i => ?_) k
        · simpa using ht
        · simpa using hx' i
      have := hS _ hmem
      rw [blockSeries_succ] at this
      simpa using this
    have hj := ih (Fin.tail ℓ)
      (fun j' => θ (Fin.cons (j 0) j' : (k : Fin (d + 1)) → Fin (splineDim q (ℓ k))))
      (Cdual * S) (hc (j 0)) (Fin.tail j)
    simp only [Fin.cons_self_tail] at hj
    calc |θ j| ≤ Cdual ^ d * (Cdual * S) := hj
      _ = Cdual ^ (d + 1) * S := by ring

end LargePrior
