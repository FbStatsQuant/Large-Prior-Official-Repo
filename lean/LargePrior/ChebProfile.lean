import LargePrior.ChebTensor
import LargePrior.ChebBasis

/-!
# Chebyshev sparse approximation profiles (Lemmas `chebyshev-profile` and `chebyshev-aniso-profile`)

Combines `ChebTensor` and `ChebBasis` against a smoothness-transfer premise to prove:
* `chebyshev_profile_core` / `chebyshev_profile_of` (D:514–531);
* `chebyshev_aniso_profile_core` / `chebyshev_aniso_profile_of` (D:601–622);
* `chebyshev_profile_at_core` / `chebyshev_profile_at_of` (empirical-norm `ProfileAt` bridge for
  Corollary 1).

The dictionary bound of both paper lemmas is `chebyshev_basis` in `ChebBasis`. Both sup-norm cores
use fold surjectivity (`chebFold_surj`) pointwise to pull the periodic bound back to `[0,1]`.
-/

open MeasureTheory Finset
open scoped Real Matrix

noncomputable section

namespace LargePrior

/-! ## Nonnegativity and positivity of `chebCapp` -/

lemma chebCapp_nonneg {d : ℕ} (hd : 0 < d) {α : Fin d → ℝ} {r : Fin d → ℕ} {CJ : Fin d → ℝ}
    {R : ℝ} (hR : 0 ≤ R) : 0 ≤ chebCapp hd α r CJ R := by
  unfold chebCapp
  have hk0 : (0 : ℝ) ≤ chebCk (α ⟨0, hd⟩) (r ⟨0, hd⟩) (CJ ⟨0, hd⟩) R :=
    mul_nonneg hR ((by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _))
  exact mul_nonneg (by positivity)
    (hk0.trans (Finset.le_sup' (fun k => chebCk (α k) (r k) (CJ k) R) (mem_univ ⟨0, hd⟩)))

lemma chebCapp_pos {d : ℕ} (hd : 0 < d) {α : Fin d → ℝ} {r : Fin d → ℕ} {CJ : Fin d → ℝ}
    {R : ℝ} (hR : 0 < R) : 0 < chebCapp hd α r CJ R := by
  unfold chebCapp
  have hk0 : (0 : ℝ) < chebCk (α ⟨0, hd⟩) (r ⟨0, hd⟩) (CJ ⟨0, hd⟩) R :=
    mul_pos hR (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_left _ _))
  exact mul_pos (by positivity)
    (lt_of_lt_of_le hk0 (Finset.le_sup' (fun k => chebCk (α k) (r k) (CJ k) R) (mem_univ ⟨0, hd⟩)))

/-! ## Univariate profile (D:514–531) -/

/-- Core univariate Chebyshev profile taking a per-order transfer premise; the coefficient map `ϑ`
is chosen before `r`, `CJ`, and `L`. -/
lemma chebyshev_profile_core {α R : ℝ} {f : ℝ → ℝ} {m : ℕ}
    (hT : ∀ r : ℕ, α < r → ChebTransferPremise α r) (hα : 0 < α) (_hR : 0 ≤ R)
    (hf : HolderBallIcc α R f) (hm : 1 ≤ m) :
    ∃ ϑ : ℕ → ℝ, (∀ j, m ≤ j → ϑ j = 0) ∧ (∀ j, |ϑ j| ≤ R) ∧
      ∀ (r : ℕ) (CJ : ℝ), α < r → JacksonIneq α r CJ →
        ∀ L : ℕ, m ≤ L → ∀ x ∈ Set.Icc (0 : ℝ) 1,
          |f x - chebSum ϑ L x| ≤ chebC α r CJ * R * (m : ℝ) ^ (-α) := by
  set g : ℝ → ℝ := f ∘ chebFold
  have hg_cont : Continuous g :=
    hf.1.continuousOn.comp_continuous chebFold_continuous chebFold_mem_Icc
  have hg_even : ∀ t, g (-t) = g t := fun t => by
    simp only [g, Function.comp_apply, chebFold_even t]
  have hg_per : Function.Periodic g 1 := fun t => by
    simp only [g, Function.comp_apply, chebFold_periodic t]
  have hg_bd : ∀ t, |g t| ≤ R := fun t => by
    simpa only [g, Function.comp_apply, iteratedDerivWithin_zero] using
      hf.2.1 0 (Nat.zero_le _) (chebFold t) (chebFold_mem_Icc t)
  obtain ⟨ϑ, hsupp, hϑ, hexp⟩ := Qop_cheb_expansion hg_cont hg_even hg_per hg_bd hm
  refine ⟨ϑ, hsupp, hϑ, fun r CJ hr hJ L hL x hx => ?_⟩
  obtain ⟨u, -, rfl⟩ := chebFold_surj x hx
  have hsum : chebSum ϑ L (chebFold u) = Qop (2 * m - 1) g u := by
    unfold chebSum
    rw [hexp L hL u]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [chebAtom_chebFold j u]
    rfl
  rw [hsum]
  exact Qop_cheb_error hα hJ hg_bd (hT r hr R f hf) hm u

/-- **Lemma `chebyshev-profile`** conditional on `ChebTransferStatement`. -/
theorem chebyshev_profile_of (hT : ChebTransferStatement) : ChebyshevProfileStatement :=
  fun α _ _ _ hα hR hf hm => chebyshev_profile_core (fun r hr => hT α r hα hr) hα hR hf hm

/-! ## Sectional anisotropic profile (D:601–622) -/

/-- Coordinatewise fold `X(u) = (x(u_1), …, x(u_d))` mapping `ℝ^d` onto `[0,1]^d`. -/
private def chebFoldVec {d : ℕ} (u : Fin d → ℝ) : Fin d → ℝ := fun k => chebFold (u k)

private lemma chebFoldVec_mem_unitCube {d : ℕ} (u : Fin d → ℝ) : chebFoldVec u ∈ unitCube d :=
  fun k => chebFold_mem_Icc (u k)

private lemma chebFoldVec_continuous {d : ℕ} : Continuous (chebFoldVec (d := d)) :=
  continuous_pi fun k => chebFold_continuous.comp (continuous_apply k)

private lemma chebFoldVec_update_neg {d : ℕ} (i : Fin d) (u : Fin d → ℝ) :
    chebFoldVec (Function.update u i (-u i)) = chebFoldVec u := by
  funext k
  by_cases h : k = i
  · subst h; simp only [chebFoldVec, Function.update_self, chebFold_even (u k)]
  · simp only [chebFoldVec, Function.update_of_ne h]

private lemma chebFoldVec_update_add_one {d : ℕ} (i : Fin d) (u : Fin d → ℝ) :
    chebFoldVec (Function.update u i (u i + 1)) = chebFoldVec u := by
  funext k
  by_cases h : k = i
  · subst h; simp only [chebFoldVec, Function.update_self, chebFold_periodic (u k)]
  · simp only [chebFoldVec, Function.update_of_ne h]

private lemma chebFoldVec_update {d : ℕ} (k : Fin d) (u : Fin d → ℝ) (t : ℝ) :
    chebFoldVec (Function.update u k t) = Function.update (chebFoldVec u) k (chebFold t) := by
  funext i
  by_cases h : i = k
  · subst h; simp only [chebFoldVec, Function.update_self]
  · simp only [chebFoldVec, Function.update_of_ne h]

/-- Core anisotropic Chebyshev profile taking a per-coordinate, per-order transfer premise; the
coefficient map `ϑ` is chosen before `r`, `CJ`, and `L`. -/
lemma chebyshev_aniso_profile_core {d : ℕ} (hd : 0 < d) {α : Fin d → ℝ} {R : ℝ}
    {f₀ : (Fin d → ℝ) → ℝ} {m : Fin d → ℕ}
    (hT : ∀ k (r : ℕ), α k < r → ChebTransferPremise (α k) r)
    (hα : ∀ k, 0 < α k) (_hR : 0 ≤ R) (hball : SecHolderBall α R f₀) (hm : ∀ k, 1 ≤ m k) :
    ∃ ϑ : (Fin d → ℕ) → ℝ, (∀ j, (∃ k, m k ≤ j k) → ϑ j = 0) ∧ (∀ j, |ϑ j| ≤ R) ∧
      ∀ (r : Fin d → ℕ) (CJ : Fin d → ℝ), (∀ k, α k < r k) →
        (∀ k, JacksonIneq (α k) (r k) (CJ k)) →
        ∀ L : Fin d → ℕ, (∀ k, m k ≤ L k) → ∀ x ∈ unitCube d,
          |f₀ x - chebSeries (L := L) (fun j => ϑ (fun k => (j k : ℕ))) x| ≤
            chebCapp hd α r CJ R * ∑ k, (m k : ℝ) ^ (-α k) := by
  set g : (Fin d → ℝ) → ℝ := fun u => f₀ (chebFoldVec u)
  have hg_cont : Continuous g :=
    hball.1.comp_continuous chebFoldVec_continuous chebFoldVec_mem_unitCube
  have hg_even : ∀ i u, g (Function.update u i (-u i)) = g u := fun i u => by
    simp only [g, chebFoldVec_update_neg]
  have hg_per : ∀ i u, g (Function.update u i (u i + 1)) = g u := fun i u => by
    simp only [g, chebFoldVec_update_add_one]
  have hg_bd : ∀ u, |g u| ≤ R := fun u => by
    let k₀ : Fin d := ⟨0, hd⟩
    have hsec := (hball.2 (chebFoldVec u) (chebFoldVec_mem_unitCube u) k₀).2.1
      0 (Nat.zero_le _) (chebFoldVec u k₀) (chebFoldVec_mem_unitCube u k₀)
    simpa only [g, iteratedDerivWithin_zero, sectionAt, Function.update_eq_self] using hsec
  obtain ⟨ϑ, hsupp, hϑ, hexp⟩ := Pop_cheb_expansion hg_cont hg_even hg_per hg_bd hm
  refine ⟨ϑ, hsupp, hϑ, fun r CJ hr hJ L hL x hx => ?_⟩
  choose u hu using fun k => chebFold_surj (x k) (hx k)
  have hxu : chebFoldVec u = x := funext fun k => (hu k).2
  have hsec : ∀ k v, HZBall1 (α k) (r k) (chebCtr (α k) (r k) * R) (sectionAt g v k) := by
    intro k v
    have hcomp : sectionAt g v k = sectionAt f₀ (chebFoldVec v) k ∘ chebFold := by
      funext t
      simp only [g, sectionAt, Function.comp_apply, chebFoldVec_update]
    rw [hcomp]
    exact hT k (r k) (hr k) R (sectionAt f₀ (chebFoldVec v) k)
      (hball.2 (chebFoldVec v) (chebFoldVec_mem_unitCube v) k)
  have hser : chebSeries (L := L) (fun j => ϑ (fun k => (j k : ℕ))) x =
      Pop (fun k => 2 * m k - 1) g u := by
    rw [← hxu, hexp L hL u]
    unfold chebSeries
    refine Finset.sum_congr rfl fun j _ => ?_
    unfold chebFoldVec
    rw [chebTensor_fold (fun k => (j k : ℕ)) u]
    rfl
  rw [hser, ← hxu]
  exact Pop_cheb_error hd hα hJ hg_cont hg_bd hsec hm u

/-- **Lemma `chebyshev-aniso-profile`** conditional on `ChebTransferStatement`. -/
theorem chebyshev_aniso_profile_of (hT : ChebTransferStatement) :
    ChebyshevAnisoProfileStatement :=
  fun _ hd α _ _ _ hα hR hball hm =>
    chebyshev_aniso_profile_core hd (fun k r hr => hT (α k) r (hα k) hr) hα hR hball hm

/-! ## Empirical-norm profile bridge (`ProfileAt`) -/

/-- Core empirical-norm profile for an arbitrary enumeration `e` of `ChebIdx L` and design `x` in
`unitCube d`, taking a per-coordinate, per-order transfer premise. -/
lemma chebyshev_profile_at_core {d : ℕ} (hd : 0 < d) {α : Fin d → ℝ} {r : Fin d → ℕ}
    {CJ : Fin d → ℝ} {R : ℝ} {f₀ : (Fin d → ℝ) → ℝ} {n J : ℕ} {L : Fin d → ℕ}
    {e : Fin J ≃ ChebIdx L} {x : Fin n → Fin d → ℝ}
    (hT : ∀ k (r' : ℕ), α k < r' → ChebTransferPremise (α k) r')
    (hα : ∀ k, 0 < α k) (hr : ∀ k, α k < r k) (hJ : ∀ k, JacksonIneq (α k) (r k) (CJ k))
    (hR : 0 ≤ R) (hball : SecHolderBall α R f₀) (hx : ∀ i, x i ∈ unitCube d) :
    ProfileAt (chebDesign e x) (fun i => f₀ (x i)) L α 1 (chebCapp hd α r CJ R) R := by
  intro m hm
  obtain ⟨ϑ, hsupp, hϑ, herr⟩ :=
    chebyshev_aniso_profile_core hd hT hα hR hball (fun k => (hm k).1)
  let θ : Fin J → ℝ := fun j => ϑ (fun k => ((e j) k : ℕ))
  refine ⟨θ, ?_, ?_, fun j => hϑ _⟩
  · let φ : Fin J → ChebIdx m := fun j k =>
      if h : ((e j) k : ℕ) < m k then ⟨((e j) k : ℕ), h⟩ else ⟨0, (hm k).1⟩
    have hlt : ∀ j ∈ univ.filter (fun j : Fin J => θ j ≠ 0), ∀ k, ((e j) k : ℕ) < m k := by
      intro j hj k
      simp only [mem_filter, mem_univ, true_and] at hj
      by_contra hnot
      push Not at hnot
      exact hj (hsupp (fun k' => ((e j) k' : ℕ)) ⟨k, hnot⟩)
    have hinj : Set.InjOn φ ↑(univ.filter (fun j : Fin J => θ j ≠ 0)) := by
      intro j₁ hj₁ j₂ hj₂ hEq
      have h1 := hlt j₁ (Finset.mem_coe.mp hj₁)
      have h2 := hlt j₂ (Finset.mem_coe.mp hj₂)
      apply e.injective
      funext k
      apply Fin.ext
      have hk := congrArg (fun f : ChebIdx m => (f k : ℕ)) hEq
      dsimp only [φ] at hk
      rw [dite_eq_left (h1 k), dite_eq_left (h2 k)] at hk
      exact hk
    have hcard : suppCard θ ≤ ∏ k, m k := by
      unfold suppCard
      calc (univ.filter (fun j : Fin J => θ j ≠ 0)).card
          ≤ (univ : Finset (ChebIdx m)).card :=
            Finset.card_le_card_of_injOn φ (fun _ _ => mem_univ _) hinj
        _ = ∏ k, m k := by rw [Finset.card_univ, Fintype.card_pi]; simp [Fintype.card_fin]
    have hcardR : (suppCard θ : ℝ) ≤ ((∏ k, m k : ℕ) : ℝ) := by exact_mod_cast hcard
    rw [Nat.cast_prod] at hcardR
    linarith
  · have hB : 0 ≤ chebCapp hd α r CJ R * ∑ k, (m k : ℝ) ^ (-α k) :=
      mul_nonneg (chebCapp_nonneg hd hR)
        (Finset.sum_nonneg fun k _ => Real.rpow_nonneg (Nat.cast_nonneg _) _)
    refine empNorm_le_of_abs_le hB _ fun i => ?_
    rw [Pi.sub_apply]
    have hmv : (chebDesign e x *ᵥ θ) i =
        chebSeries (L := L) (fun ν => ϑ (fun k => (ν k : ℕ))) (x i) := by
      simp only [chebDesign, designMatrix, Matrix.mulVec, dotProduct, Matrix.of_apply, θ]
      rw [Equiv.sum_comp e (fun ν : ChebIdx L =>
        chebTensor (fun k => (ν k : ℕ)) (x i) * ϑ (fun k => (ν k : ℕ)))]
      unfold chebSeries
      refine Finset.sum_congr rfl fun ν _ => mul_comm _ _
    rw [hmv]
    exact herr r CJ hr hJ L (fun k => (hm k).2) (x i) (hx i)

/-- **Empirical-norm Chebyshev profile** conditional on `ChebTransferStatement`. -/
theorem chebyshev_profile_at_of (hT : ChebTransferStatement) : ChebyshevProfileAtStatement :=
  fun _ hd α _ _ _ _ _ _ _ _ _ hα hr hJ hR hball hx =>
    chebyshev_profile_at_core hd (fun k r' hr' => hT (α k) r' (hα k) hr') hα hr hJ hR hball hx

end LargePrior
