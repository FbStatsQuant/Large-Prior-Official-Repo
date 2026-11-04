import LargePrior.CorHorseshoe
import LargePrior.EndSizes
import LargePrior.FourierProfile
import LargePrior.SplineProfile
import LargePrior.Basis
import LargePrior.BSpline

/-!
# Corollary 1 for the concrete dictionaries with the horseshoe prior (blueprint §E)

Assumption 2 is derived from the function class through the profile lemmas: Fourier
(periodic Hölder–Zygmund ball) and multiresolution B-splines.
-/

open MeasureTheory Filter Finset
open scoped Topology Matrix

noncomputable section

namespace LargePrior

/-- The support size is invariant under reindexing by an equivalence. -/
private lemma suppCard_comp_equiv {ι κ : Type*} [Fintype ι] [Fintype κ] (θ : ι → ℝ)
    (e : κ ≃ ι) : suppCard (fun j => θ (e j)) = suppCard θ := by
  unfold suppCard
  exact Finset.card_equiv e (by simp)

/-- Reindexed design matrix times reindexed coefficients is the series at the design point. -/
private lemma mulVec_designMatrix_equiv {n J : ℕ} {ι 𝒳 : Type*} [Fintype ι] (e : ι ≃ Fin J)
    (ξ : ι → 𝒳 → ℝ) (x : Fin n → 𝒳) (θ : ι → ℝ) (i : Fin n) :
    (designMatrix (fun j => ξ (e.symm j)) x *ᵥ fun j => θ (e.symm j)) i =
      ∑ ν, θ ν * ξ ν (x i) := by
  simp only [Matrix.mulVec, dotProduct, designMatrix, Matrix.of_apply]
  rw [Equiv.sum_comp e.symm (fun ν => ξ ν (x i) * θ ν)]
  exact Finset.sum_congr rfl fun ν _ => mul_comm _ _

/-- A pointwise bound at the design points gives the empirical-norm bound. -/
private lemma empNorm_sub_designMatrix_le {n J : ℕ} {ι 𝒳 : Type*} [Fintype ι] (e : ι ≃ Fin J)
    (ξ : ι → 𝒳 → ℝ) (x : Fin n → 𝒳) (θ : ι → ℝ) (g : 𝒳 → ℝ) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i, |g (x i) - ∑ ν, θ ν * ξ ν (x i)| ≤ B) :
    empNorm ((fun i => g (x i)) - designMatrix (fun j => ξ (e.symm j)) x *ᵥ
      fun j => θ (e.symm j)) ≤ B := by
  refine empNorm_le_of_abs_le hB _ fun i => ?_
  rw [Pi.sub_apply, mulVec_designMatrix_equiv]
  exact h i

/-- The column enumeration of the Fourier dictionary. -/
private def fourierEquiv {d : ℕ} (b : Fin d → ℝ) (n : ℕ) :
    FourierIdx (fourierM b n) ≃ Fin (fourierJ b n) :=
  Fintype.equivFin _

private lemma fourierX_eq {d : ℕ} (b : Fin d → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (n : ℕ) :
    fourierX b x n = designMatrix
      (fun j => fourierTensor (fun k => (((fourierEquiv b n).symm j) k : ℕ))) (x n) := rfl

/-- The column enumeration of the B-spline dictionary. -/
private def splineEquiv {d : ℕ} (q : ℕ) (b : Fin d → ℝ) (n : ℕ) :
    SplineIdx q (splineH b n) ≃ Fin (splineJ q b n) :=
  Fintype.equivFin _

private lemma splineX_eq {d : ℕ} (q : ℕ) (b : Fin d → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ)
    (n : ℕ) : splineX q b x n = designMatrix
      (fun j => splineAtom ((splineEquiv q b n).symm j)) (x n) := rfl

/-- Assumption 1 for the Fourier design matrices, with `K = 2^{d/2}`. -/
lemma fourier_basisBound {d : ℕ} (b : Fin d → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (n : ℕ) :
    BasisBound (fourierX b x n) (Real.sqrt 2 ^ d) := by
  rw [fourierX_eq]
  exact fourier_basis n (fourierJ b n) d (fun j k => (((fourierEquiv b n).symm j) k : ℕ)) (x n)

/-- Assumption 1 for the B-spline design matrices, with `K = 1`, design points in the cube. -/
lemma spline_basisBound {d q : ℕ} (hq : 1 ≤ q) (b : Fin d → ℝ) {x : ∀ n : ℕ, Fin n → Fin d → ℝ}
    (hx : ∀ n i, x n i ∈ unitCube d) (n : ℕ) : BasisBound (splineX q b x n) 1 := by
  rw [splineX_eq]
  exact bspline_basis n (splineJ q b n) d (fun _ _ => q)
    (fun j k => 2 ^ ((((splineEquiv q b n).symm j) k).1 : ℕ))
    (fun j k => ((((splineEquiv q b n).symm j) k).2 : ℕ)) (x n)
    (fun _ _ => hq) (fun _ _ => Nat.one_le_two_pow) (fun m k => hx n m k)

/-- Transfer of a sup-norm Fourier profile to the empirical profile of `fourierX` (blueprint
E.2): `C_sp = 1`, `C_app = C R`, `E = R + 1`. -/
lemma profileAt_fourier {d : ℕ} {b : Fin d → ℝ} {x : ∀ n : ℕ, Fin n → Fin d → ℝ}
    {f₀ : (Fin d → ℝ) → ℝ} {α : Fin d → ℝ} {C R : ℝ} (hC : 0 ≤ C) (hR : 0 ≤ R)
    (n : ℕ) (hprof : ∀ m : Fin d → ℕ, (∀ k, 1 ≤ m k ∧ m k ≤ 2 * fourierM b n k + 1) →
      ∃ θ : FourierIdx (fourierM b n) → ℝ, (suppCard θ : ℝ) ≤ ∏ k, (m k : ℝ) ∧
        (∀ y, |f₀ y - fourierSeries θ y| ≤ C * R * ∑ k, (m k : ℝ) ^ (-α k)) ∧
        ∀ ν, |θ ν| ≤ R) :
    ProfileAt (fourierX b x n) (fun i => f₀ (x n i)) (fun k => 2 * fourierM b n k + 1) α 1
      (C * R) (R + 1) := by
  intro m hm
  obtain ⟨θ, hs, ha, hc⟩ := hprof m hm
  rw [fourierX_eq]
  refine ⟨fun j => θ ((fourierEquiv b n).symm j), ?_, ?_,
    fun j => (hc _).trans (by linarith)⟩
  · rw [suppCard_comp_equiv, one_mul]
    exact hs
  · have hB : 0 ≤ C * R * ∑ k, (m k : ℝ) ^ (-α k) :=
      mul_nonneg (mul_nonneg hC hR) (Finset.sum_nonneg fun k _ => by positivity)
    exact empNorm_sub_designMatrix_le (fourierEquiv b n) (fun ν => fourierTensor (fun k => (ν k : ℕ))) (x n) θ
      f₀ hB fun i => ha (x n i)

/-- Transfer of a sup-norm spline profile on the cube to the empirical profile of `splineX`
(blueprint E.2), for design points in the cube. -/
lemma profileAt_spline {d q : ℕ} {b : Fin d → ℝ} {x : ∀ n : ℕ, Fin n → Fin d → ℝ}
    {f₀ : (Fin d → ℝ) → ℝ} {α : Fin d → ℝ} {Csp Capp E : ℝ} (hx : ∀ n i, x n i ∈ unitCube d)
    (hCapp : 0 ≤ Capp)
    (n : ℕ) (hprof : ∀ m : Fin d → ℕ, (∀ k, 1 ≤ m k ∧ m k ≤ splineUnionDim q (splineH b n k)) →
      ∃ θ : SplineIdx q (splineH b n) → ℝ, (suppCard θ : ℝ) ≤ Csp * ∏ k, (m k : ℝ) ∧
        (∀ y ∈ unitCube d, |f₀ y - splineSeries θ y| ≤ Capp * ∑ k, (m k : ℝ) ^ (-α k)) ∧
        ∀ ι, |θ ι| ≤ E) :
    ProfileAt (splineX q b x n) (fun i => f₀ (x n i))
      (fun k => splineUnionDim q (splineH b n k)) α Csp Capp E := by
  intro m hm
  obtain ⟨θ, hs, ha, hc⟩ := hprof m hm
  rw [splineX_eq]
  refine ⟨fun j => θ ((splineEquiv q b n).symm j), ?_, ?_,
    fun j => hc _⟩
  · rw [suppCard_comp_equiv]
    exact hs
  · have hB : 0 ≤ Capp * ∑ k, (m k : ℝ) ^ (-α k) :=
      mul_nonneg hCapp (Finset.sum_nonneg fun k _ => by positivity)
    exact empNorm_sub_designMatrix_le (splineEquiv q b n) (fun ν => splineAtom ν) (x n) θ f₀ hB
      fun i => ha (x n i) (hx n i)

/-- `R ≥ 0` for a nonempty Hölder–Zygmund ball. -/
lemma HZBall.radius_nonneg {d : ℕ} {α : Fin d → ℝ} {r : Fin d → ℕ} {R : ℝ}
    {f : (Fin d → ℝ) → ℝ} (h : HZBall α r R f) : 0 ≤ R := by
  obtain ⟨-, -, A, B, hA, hB, hAB, -⟩ := h
  linarith

/-- `b_k > 0` from `b_k ≥ β_k > 0`. -/
lemma b_pos {d : ℕ} {α b : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k)
    (hb : ∀ k, betaExp α k ≤ b k) (k : Fin d) : 0 < b k :=
  lt_of_lt_of_le ((exponents_pos hd hα).2.2.2.2 k) (hb k)

/-- **Corollary 1, Fourier dictionary, horseshoe prior.**
The classical approximation input is the coordinatewise Jackson inequality. -/
theorem cor_fourier : CorFourierStatement := by
  intro d α r CJ R hJ hα hr
  obtain ⟨C, hC, hprof⟩ := fourier_profile d α r CJ hα hr hJ
  refine ⟨1, d * (C * |R|) + 1, |R| + 1, one_pos, by positivity, by positivity, ?_⟩
  intro b f₀ x σ η μ'' cδ h hcδ hcδ1
  have hR := h.hball.radius_nonneg
  have hCR : (d : ℝ) * (C * R) ≤ d * (C * |R|) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (le_abs_self R) hC) (Nat.cast_nonneg d)
  exact cor_horseshoe d α b _ (fourierJ b) (fourierX b x) _ σ 1 (C * R) (|R| + 1)
    (d * (C * |R|) + 1) cδ (Real.sqrt 2 ^ d) η μ''
    { hd := h.hd, hα := h.hα, hb := h.hb, hsize := fourier_sizes (b_pos h.hd h.hα h.hb)
      hσ := h.hσ, hK := by positivity
      hbasis := Eventually.of_forall fun n => fourier_basisBound b x n
      hCsp := one_pos, hCapp := by positivity, hE := by positivity
      hprofile := Eventually.of_forall fun n => by
        intro m hm
        obtain ⟨θ, h1, h2, h3⟩ := profileAt_fourier hC hR n
          (fun m hm => hprof R f₀ (fourierM b n) m h.hball hm) m hm
        exact ⟨θ, h1, h2, fun j => (h3 j).trans (by linarith [le_abs_self R])⟩
      hCeps := by positivity, hCepsApp := by linarith, hcδ := hcδ, hcδ1 := hcδ1
      hη := h.hη, hη1 := h.hη1, hμ'' := h.hμ'' }

/-- **Corollary 1, multiresolution B-splines (rectangular levels), horseshoe prior.**
The classical inputs are B-spline readout and rectangular one-block approximation. -/
theorem cor_bspline : CorBSplineStatement := by
  intro d q α Cstar Cdual R hq hα hCstar hCdual hread
  obtain ⟨Csp, Capp, E, hCsp, hCapp, hE, hprof⟩ :=
    bspline_profile d q α Cstar Cdual R hq hα hCstar hCdual hread
  refine ⟨Csp, d * Capp + 1, E, hCsp, by positivity, hE, ?_⟩
  intro b f₀ x σ η μ'' cδ hOB h hcδ hcδ1
  exact cor_horseshoe d α b _ (splineJ q b) (splineX q b x) _ σ Csp Capp E
    (d * Capp + 1) cδ 1 η μ''
    { hd := h.hd, hα := h.hα, hb := h.hb, hsize := spline_sizes h.hq (b_pos h.hd h.hα h.hb)
      hσ := h.hσ, hK := one_pos
      hbasis := Eventually.of_forall fun n => spline_basisBound h.hq b h.hx n
      hCsp := hCsp, hCapp := hCapp, hE := hE
      hprofile := Eventually.of_forall fun n =>
        profileAt_spline h.hx hCapp n (fun m hm => hprof (splineH b n) f₀ m h.hf₀ hOB hm)
      hCeps := by positivity, hCepsApp := by linarith, hcδ := hcδ, hcδ1 := hcδ1
      hη := h.hη, hη1 := h.hη1, hμ'' := h.hμ'' }

/-- **Corollary 1, isotropic B-spline case, horseshoe prior.**
The classical inputs are B-spline readout and common-level one-block approximation. -/
theorem cor_bspline_cube : CorBSplineCubeStatement := by
  intro d q α Cstar Cdual R hd hq hα hCstar hCdual hread
  obtain ⟨Csp, Capp, E, hCsp, hCapp, hE, hprof⟩ :=
    bspline_profile_cube d q α Cstar Cdual R hd hq hα hCstar hCdual hread
  refine ⟨Csp, d * Capp + 1, E, hCsp, by positivity, hE, ?_⟩
  intro b f₀ x σ η μ'' cδ hOB h hcδ hcδ1
  exact cor_horseshoe d (fun _ => α) (fun _ => b) _ (splineJ q fun _ => b)
    (splineX q (fun _ => b) x) _ σ Csp Capp E (d * Capp + 1) cδ 1 η μ''
    { hd := h.hd, hα := h.hα, hb := h.hb
      hsize := spline_sizes h.hq (b_pos h.hd h.hα h.hb)
      hσ := h.hσ, hK := one_pos
      hbasis := Eventually.of_forall fun n => spline_basisBound h.hq _ h.hx n
      hCsp := hCsp, hCapp := hCapp, hE := hE
      hprofile := Eventually.of_forall fun n =>
        profileAt_spline (α := fun _ => α) h.hx hCapp n
          (fun m hm => hprof ⌈b * Real.logb 2 n⌉₊ f₀ m h.hf₀ hOB hm)
      hCeps := by positivity, hCepsApp := by linarith, hcδ := hcδ, hcδ1 := hcδ1
      hη := h.hη, hη1 := h.hη1, hμ'' := h.hμ'' }

end LargePrior
