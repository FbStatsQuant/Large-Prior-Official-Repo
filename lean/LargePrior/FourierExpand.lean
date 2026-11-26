import LargePrior.FourierTensor

/-!
# Tensorization: the output of `Pop` in the tensor atoms (`eq:tensor-coefficients`)

`P_m f` is a combination of the tensor atoms `Ψ_ν` with `ν_k < budgetAtoms m_k`, with
coefficients bounded by `sup |f|` (multipliers in `[0,1]`, `∫₀¹ |ψ| ≤ 1`).
-/

open MeasureTheory Finset
open scoped Real

noncomputable section

namespace LargePrior

private lemma fourierAtom_zero_eq (t : ℝ) : fourierAtom 0 t = 1 := by simp [fourierAtom]

private lemma fourierTensor_update {d : ℕ} (μ : Fin d → ℕ) (x : Fin d → ℝ) (k : Fin d) (t : ℝ) :
    fourierTensor μ (Function.update x k t) =
      fourierAtom (μ k) t * fourierTensor (Function.update μ k 0) x := by
  unfold fourierTensor
  rw [Fintype.prod_eq_mul_prod_compl k, Fintype.prod_eq_mul_prod_compl k]
  simp only [Function.update_self, fourierAtom_zero_eq, one_mul]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  have hik : i ≠ k := by simpa using hi
  rw [Function.update_of_ne hik, Function.update_of_ne hik]

private lemma tensor_update_idx {d : ℕ} {M : Fin d → ℕ} (ν : FourierIdx M) (x : Fin d → ℝ)
    (k : Fin d) (t : ℝ) :
    fourierTensor (fun k' => (ν k' : ℕ)) (Function.update x k t) =
      fourierAtom (ν k) t * fourierTensor (fun k' => ((Function.update ν k 0) k' : ℕ)) x := by
  rw [fourierTensor_update]
  congr 2
  funext k'
  by_cases h : k' = k
  · subst h; simp
  · simp [Function.update_of_ne h]

private lemma sum_reindex {d : ℕ} {M : Fin d → ℕ} (k : Fin d)
    (Φ : Fin (2 * M k + 1) → FourierIdx M → ℝ) :
    ∑ ν : FourierIdx M, Φ (ν k) (Function.update ν k 0) =
      ∑ μ : FourierIdx M, if μ k = 0 then ∑ i, Φ i μ else 0 := by
  rw [← Finset.sum_filter, ← Finset.sum_product' _ _ (fun μ i => Φ i μ)]
  apply Finset.sum_nbij' (fun ν => (Function.update ν k 0, ν k))
    (fun p => Function.update p.1 k p.2)
  · intro ν _; simp
  · intro p _; simp
  · intro ν _; simp
  · intro p hp
    simp only [mem_product, mem_filter, mem_univ, true_and, and_true] at hp
    ext : 1
    · simp only [Function.update_idem]
      conv_rhs => rw [← Function.update_eq_self k p.1]
      rw [hp]
    · simp
  · intro ν _; rfl

private lemma sum_range_eq_sum_fin {N b : ℕ} (hb : b ≤ N) (F : ℕ → ℝ) :
    ∑ j ∈ range b, F j = ∑ i : Fin N, if (i : ℕ) < b then F i else 0 := by
  rw [Fin.sum_univ_eq_sum_range (fun i => if i < b then F i else 0) N, ← Finset.sum_filter]
  congr 1
  ext j; simp; omega

private lemma coef_eq_zero_of {g : ℝ → ℝ} (hg : ∀ t, g t = 0) (j : ℕ) : coef g j = 0 := by
  unfold coef; simp [hg]

private lemma continuous_coef_section {d : ℕ} {c : (Fin d → ℝ) → ℝ} (hc : Continuous c)
    (k : Fin d) (j : ℕ) : Continuous (fun x => coef (sectionAt c x k) j) := by
  unfold coef sectionAt
  apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
  exact (hc.comp (continuous_fst.update k continuous_snd)).mul
    ((continuous_fourierAtom j).comp continuous_snd)

/-- Invariant of the expansion after processing the coordinates in `κ` (`eq:tensor-coefficients`). -/
private def ExpInv {d : ℕ} (M m : Fin d → ℕ) (A : ℝ) (κ : List (Fin d))
    (g : (Fin d → ℝ) → ℝ) : Prop :=
  ∃ c : FourierIdx M → (Fin d → ℝ) → ℝ,
    (∀ x, g x = ∑ ν, c ν x * fourierTensor (fun k => (ν k : ℕ)) x) ∧
    (∀ ν x, c ν x ≠ 0 →
      (∀ k ∈ κ, (ν k : ℕ) < budgetAtoms (m k)) ∧ (∀ k ∉ κ, (ν k : ℕ) = 0)) ∧
    (∀ ν, Continuous (c ν)) ∧
    (∀ ν x, |c ν x| ≤ A) ∧
    (∀ ν x y, (∀ k ∉ κ, x k = y k) → c ν x = c ν y)

/-- New coefficients after applying `Q^{(k)}_{m_k}`. -/
private def stepCoef {d : ℕ} {M : Fin d → ℕ} (m : Fin d → ℕ) (k : Fin d)
    (c : FourierIdx M → (Fin d → ℝ) → ℝ) (ν : FourierIdx M) (x : Fin d → ℝ) : ℝ :=
  if (ν k : ℕ) < budgetAtoms (m k) then
    qMult (m k) (freq (ν k)) * coef (sectionAt (c (Function.update ν k 0)) x k) (ν k)
  else 0

private lemma continuous_section {d : ℕ} {c : (Fin d → ℝ) → ℝ} (hc : Continuous c)
    (x : Fin d → ℝ) (k : Fin d) : Continuous (sectionAt c x k) :=
  hc.comp (continuous_const.update k continuous_id)

private lemma expInv_base {d : ℕ} {M m : Fin d → ℕ} {A : ℝ} {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hA : ∀ x, |f x| ≤ A) (hA0 : 0 ≤ A) : ExpInv M m A [] f := by
  refine ⟨fun ν x => if ν = 0 then f x else 0, ?_, ?_, ?_, ?_, ?_⟩
  · intro x
    rw [Finset.sum_eq_single (0 : FourierIdx M)]
    · simp [fourierTensor, fourierAtom_zero_eq]
    · intro ν _ hν; simp [hν]
    · intro h; exact absurd (mem_univ _) h
  · intro ν x hne
    by_cases hν : ν = 0
    · subst hν; simp
    · simp [hν] at hne
  · intro ν; by_cases hν : ν = 0
    · simp only [hν, ↓reduceIte]; exact hf
    · simp only [hν, ↓reduceIte]; exact continuous_const
  · intro ν x; by_cases hν : ν = 0
    · simp only [hν, ↓reduceIte]; exact hA x
    · simp only [hν, ↓reduceIte, abs_zero]; exact hA0
  · intro ν x y hxy
    have : x = y := funext fun k => hxy k (List.not_mem_nil)
    rw [this]

/-- Summand of the step identity, indexed by the new `k`-th index `i` and the old index `μ`. -/
private def stepTerm {d : ℕ} {M : Fin d → ℕ} (m : Fin d → ℕ) (k : Fin d)
    (c : FourierIdx M → (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (i : Fin (2 * M k + 1))
    (μ : FourierIdx M) : ℝ :=
  if (i : ℕ) < budgetAtoms (m k) then
    qMult (m k) (freq i) * coef (sectionAt (c μ) x k) i * fourierAtom i (x k) *
      fourierTensor (fun k' => (μ k' : ℕ)) x
  else 0

/-- The representation identity in the step at coordinate `k`. -/
private lemma step_eq {d : ℕ} {M m : Fin d → ℕ} (k : Fin d)
    (hb : budgetAtoms (m k) ≤ 2 * M k + 1) {g : (Fin d → ℝ) → ℝ}
    {c : FourierIdx M → (Fin d → ℝ) → ℝ}
    (hrep : ∀ x, g x = ∑ ν, c ν x * fourierTensor (fun k => (ν k : ℕ)) x)
    (hcont : ∀ ν, Continuous (c ν)) (hzero : ∀ ν x, (ν k : ℕ) ≠ 0 → c ν x = 0)
    (x : Fin d → ℝ) :
    Qcoord (m k) k g x = ∑ ν, stepCoef m k c ν x * fourierTensor (fun k => (ν k : ℕ)) x := by
  have hsec : sectionAt g x k = fun t => ∑ ν : FourierIdx M,
      fourierTensor (fun k' => ((Function.update ν k 0) k' : ℕ)) x *
        sectionAt (c ν) x k t := by
    funext t
    unfold sectionAt; rw [hrep]
    apply Finset.sum_congr rfl; intro ν _
    rw [tensor_update_idx]
    by_cases hν : (ν k : ℕ) = 0
    · rw [hν, fourierAtom_zero_eq]; ring
    · rw [hzero ν _ hν]; ring
  unfold Qcoord
  rw [hsec, Qop_finset_sum univ (fun (ν : FourierIdx M) t => fourierTensor (fun k' => ((Function.update ν k 0) k' : ℕ)) x *
        sectionAt (c ν) x k t) (fun ν _ => continuous_const.mul (continuous_section (hcont ν) x k))]
  simp only [Qop_const_mul]
  have hR : ∀ ν : FourierIdx M, stepCoef m k c ν x * fourierTensor (fun k => (ν k : ℕ)) x =
      stepTerm m k c x (ν k) (Function.update ν k 0) := by
    intro ν
    have h := tensor_update_idx ν x k (x k)
    rw [Function.update_eq_self] at h
    rw [h]
    unfold stepCoef stepTerm
    split_ifs <;> ring
  rw [Finset.sum_congr rfl (fun ν _ => hR ν), sum_reindex k (stepTerm m k c x)]
  apply Finset.sum_congr rfl
  intro μ _
  by_cases hμ : μ k = 0
  · rw [ite_eq_left hμ]
    have hupd : Function.update μ k 0 = μ := by
      rw [← hμ, Function.update_eq_self]
    rw [hupd]
    unfold Qop stepTerm
    rw [Finset.mul_sum, sum_range_eq_sum_fin hb]
    apply Finset.sum_congr rfl
    intro i _
    split_ifs <;> ring
  · rw [ite_eq_right hμ]
    have hμ' : (μ k : ℕ) ≠ 0 := fun h => hμ (Fin.ext h)
    have hQ : Qop (m k) (sectionAt (c μ) x k) (x k) = 0 := by
      unfold Qop
      apply Finset.sum_eq_zero
      intro j _
      rw [coef_eq_zero_of (g := sectionAt (c μ) x k) (fun t => hzero μ _ hμ') j]
      ring
    rw [hQ, mul_zero]

private lemma expInv_step {d : ℕ} {M m : Fin d → ℕ} {A : ℝ} (hA0 : 0 ≤ A)
    (hb : ∀ k, budgetAtoms (m k) ≤ 2 * M k + 1) {κ : List (Fin d)} {k : Fin d} (hk : k ∉ κ)
    {g : (Fin d → ℝ) → ℝ} (hg : ExpInv M m A κ g) :
    ExpInv M m A (k :: κ) (Qcoord (m k) k g) := by
  obtain ⟨c, hrep, hsupp, hcont, hbd, hinv⟩ := hg
  have hzero : ∀ ν x, (ν k : ℕ) ≠ 0 → c ν x = 0 := by
    intro ν x hν; by_contra h; exact hν ((hsupp ν x h).2 k hk)
  refine ⟨stepCoef m k c, step_eq k (hb k) hrep hcont hzero, ?_, ?_, ?_, ?_⟩
  · intro ν x hne
    unfold stepCoef at hne
    split_ifs at hne with hlt
    · have hcoef : coef (sectionAt (c (Function.update ν k 0)) x k) (ν k) ≠ 0 :=
        fun h => hne (by rw [h, mul_zero])
      obtain ⟨t, ht⟩ : ∃ t, sectionAt (c (Function.update ν k 0)) x k t ≠ 0 := by
        by_contra hall
        push Not at hall
        exact hcoef (coef_eq_zero_of hall _)
      obtain ⟨h1, h2⟩ := hsupp _ _ ht
      constructor
      · intro k' hk'
        rcases List.mem_cons.mp hk' with rfl | hk'
        · exact hlt
        · have hne' : k' ≠ k := fun h => hk (h ▸ hk')
          simpa [Function.update_of_ne hne'] using h1 k' hk'
      · intro k' hk'
        have hne' : k' ≠ k := fun h => hk' (h ▸ List.mem_cons_self ..)
        have hk'' : k' ∉ κ := fun h => hk' (List.mem_cons_of_mem _ h)
        simpa [Function.update_of_ne hne'] using h2 k' hk''
    · exact absurd rfl hne
  · intro ν
    unfold stepCoef
    split_ifs
    · exact continuous_const.mul (continuous_coef_section (hcont _) k _)
    · exact continuous_const
  · intro ν x
    unfold stepCoef
    split_ifs
    · rw [abs_mul]
      have hq := qMult_mem_Icc (m k) (freq (ν k))
      have hcf := coef_abs_le (continuous_section (hcont (Function.update ν k 0)) x k)
        (fun t => hbd _ _) (ν k)
      rw [abs_of_nonneg hq.1]
      calc _ ≤ 1 * A := mul_le_mul hq.2 hcf (abs_nonneg _) zero_le_one
        _ = A := one_mul A
    · simpa using hA0
  · intro ν x y hxy
    unfold stepCoef
    split_ifs
    · congr 2
      funext t
      unfold sectionAt
      apply hinv
      intro k' hk'
      by_cases hkk : k' = k
      · subst hkk; simp
      · rw [Function.update_of_ne hkk, Function.update_of_ne hkk]
        exact hxy k' (by simp [hkk, hk'])
    · rfl

private lemma expInv_foldr {d : ℕ} {M m : Fin d → ℕ} {A : ℝ} {f : (Fin d → ℝ) → ℝ}
    (hf : Continuous f) (hA : ∀ x, |f x| ≤ A) (hA0 : 0 ≤ A)
    (hb : ∀ k, budgetAtoms (m k) ≤ 2 * M k + 1) :
    ∀ κ : List (Fin d), κ.Nodup →
      ExpInv M m A κ (κ.foldr (fun k g => Qcoord (m k) k g) f)
  | [], _ => expInv_base hf hA hA0
  | k :: κ, h => by
      rw [List.nodup_cons] at h
      exact expInv_step hA0 hb h.1 (expInv_foldr hf hA hA0 hb κ h.2)

/-- **Expansion of `P_m f`** (eq:tensor-coefficients): for continuous `f` with `|f| ≤ A` and a
rectangle `1 ≤ m_k ≤ 2M_k + 1`, there is `θ` on `F_M` with `#supp θ ≤ ∏_k budgetAtoms m_k`
(in the construction, `θ` vanishes outside the rectangle `{ν : ν_k < budgetAtoms m_k}`), with
`|θ_ν| ≤ A`, and `P_m f = f_θ` everywhere. -/
lemma Pop_expansion {d : ℕ} {f : (Fin d → ℝ) → ℝ} {A : ℝ} (hf : Continuous f)
    (hA : ∀ x, |f x| ≤ A) (M m : Fin d → ℕ) (hm : ∀ k, 1 ≤ m k ∧ m k ≤ 2 * M k + 1) :
    ∃ θ : FourierIdx M → ℝ, (suppCard θ : ℝ) ≤ ∏ k, (budgetAtoms (m k) : ℝ) ∧
      (∀ ν, |θ ν| ≤ A) ∧ ∀ x, Pop m f x = fourierSeries θ x := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hb : ∀ k, budgetAtoms (m k) ≤ 2 * M k + 1 :=
    fun k => (budgetAtoms_le (hm k).1).trans (hm k).2
  obtain ⟨c, hrep, hsupp, -, hbd, hinv⟩ :=
    expInv_foldr (M := M) hf hA hA0 hb (List.finRange d) (List.nodup_finRange d)
  have hconst : ∀ ν x, c ν x = c ν 0 :=
    fun ν x => hinv ν x 0 (fun k hk => absurd (List.mem_finRange k) hk)
  refine ⟨fun ν => c ν 0, ?_, fun ν => hbd ν 0, ?_⟩
  · have hsub : univ.filter (fun ν => c ν 0 ≠ 0) ⊆ Fintype.piFinset
        (fun k => univ.filter (fun i : Fin (2 * M k + 1) => (i : ℕ) < budgetAtoms (m k))) := by
      intro ν hν
      simp only [mem_filter, mem_univ, true_and] at hν
      rw [Fintype.mem_piFinset]
      intro k
      simp only [mem_filter, mem_univ, true_and]
      exact (hsupp ν 0 hν).1 k (List.mem_finRange k)
    have hcard := card_le_card hsub
    rw [Fintype.card_piFinset] at hcard
    have hfin : ∀ k, (univ.filter (fun i : Fin (2 * M k + 1) =>
        (i : ℕ) < budgetAtoms (m k))).card = budgetAtoms (m k) := by
      intro k
      rw [Fin.card_filter_val_lt, min_eq_right (hb k)]
    simp only [hfin] at hcard
    unfold suppCard
    exact_mod_cast hcard
  · intro x
    unfold Pop fourierSeries
    rw [hrep x]
    apply Finset.sum_congr rfl
    intro ν _
    rw [hconst ν x]

end LargePrior
