import LargePrior.VdP

/-!
# Tensorization of the univariate smoother: error bound (blueprint §F.4)

`Qcoord m k` applies `Q_m` to the `k`-th coordinate; `Pop m = Q^{(0)}_{m_0} ∘ ⋯ ∘ Q^{(d−1)}_{m_{d−1}}`
(rightmost first). The error of `Pop m` telescopes into one univariate error per coordinate.
-/

open MeasureTheory Finset
open scoped Real

noncomputable section

namespace LargePrior

/-- `Q_m` acting on the `k`-th coordinate: `(Q^{(k)}_m f)(x) = (Q_m g_{x,k})(x_k)`, with
`g_{x,k}` the section of `f` through `x` in direction `k`. -/
def Qcoord {d : ℕ} (m : ℕ) (k : Fin d) (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  fun x => Qop m (sectionAt f x k) (x k)

/-- `P_m f = Q^{(0)}_{m_0}(Q^{(1)}_{m_1}(⋯ Q^{(d−1)}_{m_{d−1}} f))`. -/
def Pop {d : ℕ} (m : Fin d → ℕ) (f : (Fin d → ℝ) → ℝ) : (Fin d → ℝ) → ℝ :=
  (List.finRange d).foldr (fun k g => Qcoord (m k) k g) f

private lemma sectionAt_continuous {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (x : Fin d → ℝ) (k : Fin d) : Continuous (sectionAt f x k) :=
  hf.comp (continuous_const.update k continuous_id)

private lemma update_add_single {d : ℕ} (x : Fin d → ℝ) (k : Fin d) (t : ℝ) :
    Function.update x k (t + 1) = Function.update x k t + Pi.single k 1 := by
  funext j
  by_cases hj : j = k
  · subst hj; simp
  · simp [hj]

private lemma sectionAt_update {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (k : Fin d) (t : ℝ) :
    sectionAt f (Function.update x k t) k = sectionAt f x k := by
  funext s
  simp [sectionAt, Function.update_idem]

/-- Every section of a function in the anisotropic ball lies in the univariate ball. -/
private lemma sectionAt_mem_HZBall1 {d : ℕ} {α : Fin d → ℝ} {r : Fin d → ℕ} {R : ℝ}
    {f₀ : (Fin d → ℝ) → ℝ} (hball : HZBall α r R f₀) (k : Fin d) (x : Fin d → ℝ) :
    HZBall1 (α k) (r k) R (sectionAt f₀ x k) := by
  obtain ⟨hc, hper, A, B, hA0, hB0, hAB, hAbd, hdiff⟩ := hball
  refine ⟨sectionAt_continuous hc x k, fun t => ?_, A, B, hA0, hB0, hAB, fun t => hAbd _,
    fun h t h0 h1 => ?_⟩
  · simp only [sectionAt]
    rw [update_add_single, hper]
  · have := hdiff k (Function.update x k t) h h0 h1
    rwa [sectionAt_update, Function.update_self] at this

/-- `Q^{(k)}_m` preserves continuity. -/
lemma Qcoord_continuous {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (m : ℕ) (k : Fin d) :
    Continuous (Qcoord m k f) := by
  unfold Qcoord Qop
  refine continuous_finsetSum _ fun ν _ => ?_
  refine Continuous.mul (continuous_const.mul ?_) ((continuous_fourierAtom ν).comp (continuous_apply k))
  unfold coef sectionAt
  refine intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    (f := fun x t => f (Function.update x k t) * fourierAtom ν t) ?_ 0 1
  exact (hf.comp (continuous_fst.update k continuous_snd)).mul
    ((continuous_fourierAtom ν).comp continuous_snd)

/-- Coordinatewise stability: `|Q^{(k)}_m f| ≤ 3A` when `f` is continuous and `|f| ≤ A`. -/
lemma Qcoord_stable {d : ℕ} {f : (Fin d → ℝ) → ℝ} {A : ℝ} (hf : Continuous f)
    (hA : ∀ x, |f x| ≤ A) (m : ℕ) (k : Fin d) (x : Fin d → ℝ) : |Qcoord m k f x| ≤ 3 * A := by
  exact Qop_stable (sectionAt_continuous hf x k) (fun t => hA _) m (x k)

/-- Linearity of `Q^{(k)}_m` on continuous functions. -/
lemma Qcoord_sub {d : ℕ} {f g : (Fin d → ℝ) → ℝ} (hf : Continuous f) (hg : Continuous g)
    (m : ℕ) (k : Fin d) : Qcoord m k (f - g) = Qcoord m k f - Qcoord m k g := by
  funext x
  exact Qop_sub (sectionAt_continuous hf x k) (sectionAt_continuous hg x k) m (x k)

/-- Single-coordinate error bound: every section of a Hölder–Zygmund `f₀` lies in the univariate
ball, so `|f₀ − Q^{(k)}_m f₀| ≤ C'_{α_k} R m^{−α_k}`. -/
lemma Qcoord_error {d : ℕ} {α : Fin d → ℝ} {r : Fin d → ℕ} {CJ : Fin d → ℝ} {R : ℝ}
    {f₀ : (Fin d → ℝ) → ℝ} (hα : ∀ k, 0 < α k) (hJ : ∀ k, JacksonIneq (α k) (r k) (CJ k))
    (hball : HZBall α r R f₀) {m : ℕ} (hm : 1 ≤ m) (k : Fin d) (x : Fin d → ℝ) :
    |f₀ x - Qcoord m k f₀ x| ≤ jackC' (α k) (CJ k) * R * (m : ℝ) ^ (-α k) := by
  have h := Qop_error (hα k) (hJ k) (sectionAt_mem_HZBall1 hball k x) hm (x k)
  have hx : sectionAt f₀ x k (x k) = f₀ x := by simp [sectionAt, Function.update_eq_self]
  rw [hx] at h
  exact h

/-- Telescoping invariant along an arbitrary list of coordinates. -/
private lemma foldr_Qcoord_error {d : ℕ} {α : Fin d → ℝ} {r : Fin d → ℕ} {CJ : Fin d → ℝ} {R : ℝ}
    {f₀ : (Fin d → ℝ) → ℝ} (hα : ∀ k, 0 < α k) (hJ : ∀ k, JacksonIneq (α k) (r k) (CJ k))
    (hball : HZBall α r R f₀) {m : Fin d → ℕ} (hm : ∀ k, 1 ≤ m k)
    (he : ∀ k, 0 ≤ jackC' (α k) (CJ k) * R * (m k : ℝ) ^ (-α k)) (κ : List (Fin d)) :
    Continuous (κ.foldr (fun k g => Qcoord (m k) k g) f₀) ∧
    ∀ x, |f₀ x - κ.foldr (fun k g => Qcoord (m k) k g) f₀ x| ≤
      3 ^ κ.length * (κ.map fun k => jackC' (α k) (CJ k) * R * (m k : ℝ) ^ (-α k)).sum := by
  have hc0 : Continuous f₀ := hball.1
  induction κ with
  | nil => exact ⟨hc0, fun x => by simp⟩
  | cons k κ ih =>
    obtain ⟨hcont, hbd⟩ := ih
    set L := κ.foldr (fun k g => Qcoord (m k) k g) f₀ with hL
    set S := (κ.map fun k => jackC' (α k) (CJ k) * R * (m k : ℝ) ^ (-α k)).sum with hS
    refine ⟨Qcoord_continuous hcont (m k) k, fun x => ?_⟩
    simp only [List.foldr_cons, List.length_cons, List.map_cons, List.sum_cons]
    rw [← hL, ← hS]
    have hsub := congrFun (Qcoord_sub hc0 hcont (m k) k) x
    simp only [Pi.sub_apply] at hsub
    have h1 := Qcoord_error hα hJ hball (hm k) k x
    have h2 := Qcoord_stable (hc0.sub hcont) (fun y => by simpa using hbd y) (m k) k x
    rw [hsub] at h2
    have hS0 : 0 ≤ S := List.sum_nonneg (by simp; exact fun a _ => he a)
    have h31 : (1 : ℝ) ≤ 3 ^ κ.length := one_le_pow₀ (by norm_num)
    have hsplit : f₀ x - Qcoord (m k) k L x =
        (f₀ x - Qcoord (m k) k f₀ x) + (Qcoord (m k) k f₀ x - Qcoord (m k) k L x) := by ring
    rw [hsplit]
    refine (abs_add_le _ _).trans ?_
    rw [pow_succ]
    nlinarith [he k, h1, h2]

/-- **Tensor error bound** (telescoping): with `C = 3^d ∑_k C'_{α_k}`,
`|f₀ − P_m f₀| ≤ C R ∑_k m_k^{−α_k}`. -/
lemma Pop_error {d : ℕ} {α : Fin d → ℝ} {r : Fin d → ℕ} {CJ : Fin d → ℝ} {R : ℝ}
    {f₀ : (Fin d → ℝ) → ℝ} (hα : ∀ k, 0 < α k) (hJ : ∀ k, JacksonIneq (α k) (r k) (CJ k))
    (hball : HZBall α r R f₀) {m : Fin d → ℕ} (hm : ∀ k, 1 ≤ m k) (x : Fin d → ℝ) :
    |f₀ x - Pop m f₀ x| ≤
      3 ^ d * (∑ k, jackC' (α k) (CJ k)) * R * ∑ k, (m k : ℝ) ^ (-α k) := by
  have hR : 0 ≤ R := by
    obtain ⟨-, -, A, B, hA0, hB0, hAB, -⟩ := hball
    linarith
  have hC : ∀ k, 0 ≤ jackC' (α k) (CJ k) := fun k =>
    le_max_of_le_right (by positivity)
  have hmp : ∀ k, 0 ≤ (m k : ℝ) ^ (-α k) := fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have he : ∀ k, 0 ≤ jackC' (α k) (CJ k) * R * (m k : ℝ) ^ (-α k) := fun k =>
    mul_nonneg (mul_nonneg (hC k) hR) (hmp k)
  have key := (foldr_Qcoord_error hα hJ hball hm he (List.finRange d)).2 x
  rw [List.length_finRange, ← Fin.sum_univ_def] at key
  unfold Pop
  refine key.trans ?_
  have h3 : (0 : ℝ) ≤ 3 ^ d := by positivity
  rw [mul_assoc (3 ^ d : ℝ), mul_assoc (3 ^ d : ℝ)]
  refine mul_le_mul_of_nonneg_left ?_ h3
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have hk : jackC' (α k) (CJ k) ≤ ∑ j, jackC' (α j) (CJ j) :=
    Finset.single_le_sum (fun j _ => hC j) (Finset.mem_univ k)
  have := mul_le_mul_of_nonneg_right hk (mul_nonneg hR (hmp k))
  linarith [this]

end LargePrior
