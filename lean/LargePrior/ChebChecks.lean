import LargePrior.ChebTransfer
import LargePrior.ChebTransferHigh
import LargePrior.ChebEndToEnd

/-!
# Sanity checks and witnesses for the Chebyshev dictionary

The low-order class recovers the Hölder ball, the transfer constant takes the
four values in Appendix D, and the tensor profile specializes to the univariate
profile. A quadratic and a quadratic-linear product witness the higher-order class.
Two unconditional witnesses (`cor_chebyshev_witness_two`, `cor_chebyshev_witness_one`)
instantiate `cor_chebyshev_holder` at `d = 2` and `d = 1`.
-/

open scoped ENNReal NNReal

noncomputable section

namespace LargePrior

/-- The interval class agrees with the order-zero Hölder class for `0 < α ≤ 1`. -/
theorem cheb_sanity_holder : ChebSanityHolder := by
  intro α R f hα hα1
  rw [HolderBallIcc, chebBeta_of_le_one hα1, chebS_of_le_one hα1]
  simp only [Nat.cast_zero, contDiffOn_zero, Nat.le_zero, forall_eq,
    iteratedDerivWithin_zero]
  constructor
  · exact fun h => h.2
  · intro h
    have hR : 0 ≤ R :=
      (abs_nonneg _).trans (h.1 0 (Set.left_mem_Icc.mpr zero_le_one))
    let C : ℝ≥0 := ⟨R, hR⟩
    let p : ℝ≥0 := ⟨α, hα.le⟩
    have hHold : HolderOnWith C p f (Set.Icc 0 1) := by
      intro x hx y hy
      rw [edist_dist, edist_dist, Real.dist_eq, Real.dist_eq]
      change ENNReal.ofReal |f x - f y| ≤ (C : ℝ≥0∞) * (ENNReal.ofReal |x - y|) ^ α
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg (x - y)) hα.le,
        ← ENNReal.ofReal_coe_nnreal]
      change ENNReal.ofReal |f x - f y| ≤ ENNReal.ofReal R * ENNReal.ofReal (|x - y| ^ α)
      rw [← ENNReal.ofReal_mul hR]
      exact ENNReal.ofReal_le_ofReal (h.2 x hx y hy)
    exact ⟨hHold.continuousOn hα, h⟩

/-- The four displayed values of the transfer constant at the smallest admissible order. -/
theorem cheb_sanity_ctr : ChebSanityCtr := by
  have hfloor : ⌊(1 / 2 : ℝ)⌋₊ = 0 := Nat.floor_eq_zero.mpr (by norm_num)
  have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by
    ext k
    simp only [Finset.mem_Icc, Finset.mem_insert, Finset.mem_singleton]
    omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [chebCtr_of_le_one _ (by norm_num), hfloor, Real.sqrt_eq_rpow]
    norm_num
  · rw [chebCtr_of_le_one _ le_rfl]
    norm_num [Nat.floor_one]
  · norm_num [chebCtr, chebS, chebBeta, chebKappa, Nat.floor_ofNat, Nat.ceil_ofNat,
      Finset.Icc_self, Nat.stirlingSecond_self]
    ring
  · norm_num [chebCtr, chebS, chebBeta, chebKappa, Nat.floor_ofNat, Nat.ceil_ofNat,
      hIcc, Nat.stirlingSecond_one_right, Nat.stirlingSecond_self]
    ring

private lemma chebSeries_one_eq (L : Fin 1 → ℕ) (ϑ : ℕ → ℝ) (x : Fin 1 → ℝ) :
    chebSeries (L := L) (fun j => ϑ (j 0 : ℕ)) x = chebSum ϑ (L 0) (x 0) := by
  unfold chebSeries chebSum chebTensor
  simp only [Fin.prod_univ_one]
  rw [← Fin.sum_univ_eq_sum_range (fun j => ϑ j * chebAtom j (x 0))]
  exact Fintype.sum_equiv (Equiv.piUnique _) _ _ (fun j => rfl)

/-- The one-coordinate tensor profile has the same coefficients and bound as the scalar profile. -/
theorem cheb_sanity_aniso_univ : ChebSanityAnisoUniv := by
  intro hAniso α R f m hα hR hf hm
  let g : (Fin 1 → ℝ) → ℝ := fun x => f (x 0)
  have hsec (x : Fin 1 → ℝ) : sectionAt g x 0 = f := by
    funext t
    simp only [sectionAt, g, Function.update_self]
  have hg : SecHolderBall (fun _ : Fin 1 => α) R g := by
    refine ⟨hf.1.continuousOn.comp (continuous_apply 0).continuousOn (fun _ hx => hx 0), ?_⟩
    intro x _ k
    have hk : k = 0 := Subsingleton.elim _ _
    subst k
    rw [hsec]
    exact hf
  obtain ⟨ϑ, hSupp, hBound, hError⟩ :=
    hAniso 1 (by decide) (fun _ => α) R g (fun _ => m) (fun _ => hα) hR hg (fun _ => hm)
  refine ⟨fun j => ϑ (fun _ => j), fun j hj => hSupp _ ⟨0, hj⟩, fun j => hBound _, ?_⟩
  intro r CJ hr hJackson L hL x hx
  have h := hError (fun _ => r) (fun _ => CJ) (fun _ => hr) (fun _ => hJackson)
    (fun _ => L) (fun _ => hL) (fun _ => x) (fun _ => hx)
  have hj (j : ChebIdx (fun _ : Fin 1 => L)) :
      (fun k : Fin 1 => (j k : ℕ)) = (fun _ : Fin 1 => (j 0 : ℕ)) := by
    funext k
    rw [show k = 0 from Subsingleton.elim _ _]
  simp only [hj] at h
  rw [chebSeries_one_eq (fun _ : Fin 1 => L) (fun j => ϑ (fun _ => j)) (fun _ => x)] at h
  simp only [g, chebCapp, chebCk, Finset.univ_unique, Finset.sup'_singleton,
    Nat.sub_self, pow_zero, one_mul, Finset.sum_singleton] at h
  simpa only [mul_comm R (chebC α r CJ)] using h

private lemma holderBallIcc_mul_sq {a : ℝ} (ha : a ∈ Set.Icc (0 : ℝ) 1) :
    HolderBallIcc 2 2 (fun y : ℝ => a * y ^ 2) := by
  have hs : chebS 2 = 1 := by norm_num [chebS, Nat.ceil_ofNat]
  have hb : chebBeta 2 = 1 := by norm_num [chebBeta, hs]
  have hderiv (y : ℝ) (hy : y ∈ Set.Icc (0 : ℝ) 1) :
      iteratedDerivWithin 1 (fun t : ℝ => a * t ^ 2) (Set.Icc 0 1) y = a * (2 * y) := by
    rw [iteratedDerivWithin_one]
    have h : HasDerivAt (fun t : ℝ => a * t ^ 2) (a * (2 * y)) y := by
      simpa [id] using ((hasDerivAt_id y).fun_pow 2).const_mul a
    exact h.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc_zero_one y hy)
  rw [HolderBallIcc, hs, hb]
  refine ⟨?_, ?_, ?_⟩
  · apply ContDiff.contDiffOn
    fun_prop
  · intro j hj y hy
    have ha0 := ha.1
    have hy0 := hy.1
    rcases (show j = 0 ∨ j = 1 by omega) with rfl | rfl
    · rw [iteratedDerivWithin_zero, abs_of_nonneg (by positivity)]
      have hy2 : y ^ 2 ≤ 1 := by
        nlinarith [hy.2, mul_nonneg hy0 (sub_nonneg.mpr hy.2)]
      calc
        a * y ^ 2 ≤ 1 * 1 := mul_le_mul ha.2 hy2 (sq_nonneg _) zero_le_one
        _ ≤ 2 := by norm_num
    · rw [hderiv y hy, abs_of_nonneg (by positivity)]
      calc
        a * (2 * y) ≤ 1 * 2 :=
          mul_le_mul ha.2 (by linarith [hy.2]) (by positivity) zero_le_one
        _ = 2 := one_mul _
  · intro y hy z hz
    rw [hderiv y hy, hderiv z hz, Real.rpow_one,
      show a * (2 * y) - a * (2 * z) = (2 * a) * (y - z) by ring,
      abs_mul, abs_of_nonneg (mul_nonneg zero_le_two ha.1)]
    exact mul_le_mul_of_nonneg_right (by linarith [ha.2]) (abs_nonneg _)

private lemma holderBallIcc_linear {α R a : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (ha : |a| ≤ R) :
    HolderBallIcc α R (fun y => a * y) := by
  apply (cheb_sanity_holder α R _ hα hα1).2
  constructor
  · intro y hy
    rw [abs_mul, abs_of_nonneg hy.1]
    exact (mul_le_of_le_one_right (abs_nonneg a) hy.2).trans ha
  · intro y hy z hz
    have hdist : |y - z| ≤ 1 :=
      abs_le.mpr ⟨by linarith [hy.1, hz.2], by linarith [hy.2, hz.1]⟩
    have hpow : |y - z| ≤ |y - z| ^ α := by
      simpa only [Real.rpow_one] using
        Real.rpow_le_rpow_of_exponent_ge' (abs_nonneg _) hdist hα.le hα1
    rw [← mul_sub, abs_mul]
    exact mul_le_mul ha hpow (abs_nonneg _) ((abs_nonneg a).trans ha)

/-- The quadratic belongs to the interval Hölder ball at smoothness and radius two. -/
theorem cheb_witness_sq : HolderBallIcc 2 2 (fun x : ℝ => x ^ 2) := by
  simpa only [one_mul] using holderBallIcc_mul_sq (a := 1) ⟨zero_le_one, le_rfl⟩

/-- The quadratic transfers to the periodic ball at difference order three. -/
theorem cheb_witness_sq_transfer :
    HZBall1 2 3 (chebCtr 2 3 * 2) ((fun x : ℝ => x ^ 2) ∘ chebFold) :=
  cheb_transfer (α := 2) (r := 3) (by norm_num) (by norm_num) 2 _ cheb_witness_sq

/-- The transfer constant at smoothness two and difference order three. -/
theorem chebCtr_two_three : chebCtr 2 3 = 1 + 6 * Real.pi ^ 2 := by
  simpa only [Nat.floor_ofNat] using cheb_sanity_ctr.2.2.1

/-- The quadratic-linear product belongs to the sectional ball at smoothness `(2, 1/2)`. -/
theorem cheb_witness_sq_mul :
    SecHolderBall (![2, 1 / 2] : Fin 2 → ℝ) 2 (fun x => x 0 ^ 2 * x 1) := by
  constructor
  · exact (((continuous_apply (0 : Fin 2)).pow 2).mul
      (continuous_apply (1 : Fin 2))).continuousOn
  · intro x hx
    rw [Fin.forall_fin_two]
    constructor
    · have hne : (1 : Fin 2) ≠ 0 := by decide
      change HolderBallIcc 2 2
        (fun t => (Function.update x 0 t) 0 ^ 2 * (Function.update x 0 t) 1)
      simpa only [Function.update_self, Function.update_of_ne hne, mul_comm] using
        holderBallIcc_mul_sq (hx 1)
    · have hne : (0 : Fin 2) ≠ 1 := by decide
      have hA : |x 0 ^ 2| ≤ 2 := by
        have h0 := hx 0
        rw [abs_of_nonneg (sq_nonneg _)]
        nlinarith [h0.2, mul_nonneg h0.1 (sub_nonneg.mpr h0.2)]
      change HolderBallIcc (1 / 2) 2
        (fun t => (Function.update x 1 t) 0 ^ 2 * (Function.update x 1 t) 1)
      simpa only [Function.update_self, Function.update_of_ne hne] using
        holderBallIcc_linear (α := 1 / 2) (by norm_num) (by norm_num) hA

/-! ## End-to-end witnesses -/

private lemma design_fraction_mem {n : ℕ} (i : Fin n) :
    (i : ℝ) / n ∈ Set.Icc (0 : ℝ) 1 := by
  have hn : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_le i.val).trans_lt i.isLt
  exact ⟨by positivity, (div_le_one hn).2 (by exact_mod_cast i.isLt.le)⟩

private lemma cheb_holder_witness {d : ℕ} (hd : 0 < d) {α : Fin d → ℝ}
    {f₀ : (Fin d → ℝ) → ℝ} {x : ∀ n : ℕ, Fin n → Fin d → ℝ}
    (hα : ∀ k, 0 < α k) (hα1 : ∀ k, α k < 1)
    (hf : SecHolderBall α 1 f₀) (hx : ∀ n i, x n i ∈ unitCube d) :
    let b := betaExp α
    ∃ CJ : Fin d → ℝ, 0 < chebCapp hd α (fun _ => 1) CJ 1 ∧
      ∃ c5 : ℝ, 0 ≤ c5 ∧
        CorConclusion α (chebJ b) (chebX b x) (fun n i => f₀ (x n i)) 1
          (fun n => horseshoePDF (corTau 1 n (chebJ b n))) 1
          ((d : ℝ) * chebCapp hd α (fun _ => 1) CJ 1) (1 / 2)
          (Aconst (Real.sqrt 2 ^ d) (1 / 2) 1 (1 / 2) 1 c5) := by
  intro b
  obtain ⟨CJ, _, hCor⟩ := cor_chebyshev_holder d hd α hα hα1
  have hr : ∀ k, α k < ((1 : ℕ) : ℝ) := by simpa only [Nat.cast_one] using hα1
  have hHyp : CorChebHyp α b (fun _ => 1) 1 f₀ x 1 (1 / 2) 1 :=
    ⟨hα, hr, fun _ => le_rfl, one_pos, hf, hx, one_pos, by norm_num, by norm_num, one_pos⟩
  have hsize : SizesComparable b (chebL b) (chebJ b) :=
    cheb_sizes (exponents_pos hd hα).2.2.2.2
  obtain ⟨c5, hc5, _, hConclusion⟩ :=
    hCor 1 ((d : ℝ) * chebCapp hd α (fun _ => 1) CJ 1) le_rfl b (chebJ b) (chebL b)
      (fun n => (Fintype.equivFin (ChebIdx (chebL b n))).symm) f₀ x 1 (1 / 2) 1 (1 / 2)
      hHyp hsize (by norm_num) (by norm_num)
  exact ⟨CJ, chebCapp_pos hd one_pos, c5, hc5, hConclusion⟩

/-- W1: the two-coordinate corollary for the product at smoothness `(1/2, 3/4)`. -/
theorem cor_chebyshev_witness_two :
    let α : Fin 2 → ℝ := ![1 / 2, 3 / 4]
    let f₀ : (Fin 2 → ℝ) → ℝ := fun y => y 0 * y 1
    let x : (n : ℕ) → Fin n → Fin 2 → ℝ := fun n i => ![(i : ℝ) / n, 1 - (i : ℝ) / n]
    let b := betaExp α
    ∃ CJ : Fin 2 → ℝ, 0 < chebCapp (by decide) α (fun _ => 1) CJ 1 ∧
      ∃ c5 : ℝ, 0 ≤ c5 ∧
        CorConclusion α (chebJ b) (chebX b x) (fun n i => f₀ (x n i)) 1
          (fun n => horseshoePDF (corTau 1 n (chebJ b n))) 1
          (2 * chebCapp (by decide) α (fun _ => 1) CJ 1) (1 / 2)
          (Aconst (Real.sqrt 2 ^ 2) (1 / 2) 1 (1 / 2) 1 c5) := by
  intro α f₀ x
  have hα : ∀ k, 0 < α k := by rw [Fin.forall_fin_two]; norm_num [α]
  have hα1 : ∀ k, α k < 1 := by rw [Fin.forall_fin_two]; norm_num [α]
  refine cheb_holder_witness (by decide) hα hα1 (f₀ := f₀) (x := x) ?_ ?_
  · refine ⟨((continuous_apply 0).mul (continuous_apply 1)).continuousOn, ?_⟩
    intro y hy
    rw [Fin.forall_fin_two]
    constructor
    · change HolderBallIcc (1 / 2) 1
        (fun t => Function.update y 0 t 0 * Function.update y 0 t 1)
      have hne : (1 : Fin 2) ≠ 0 := by decide
      have ha : |y 1| ≤ 1 := by rw [abs_of_nonneg (hy 1).1]; exact (hy 1).2
      simpa only [Function.update_self, Function.update_of_ne hne, mul_comm] using
        holderBallIcc_linear (α := 1 / 2) (by norm_num) (by norm_num) ha
    · change HolderBallIcc (3 / 4) 1
        (fun t => Function.update y 1 t 0 * Function.update y 1 t 1)
      have hne : (0 : Fin 2) ≠ 1 := by decide
      have ha : |y 0| ≤ 1 := by rw [abs_of_nonneg (hy 0).1]; exact (hy 0).2
      simpa only [Function.update_self, Function.update_of_ne hne] using
        holderBallIcc_linear (α := 3 / 4) (by norm_num) (by norm_num) ha
  · intro n i
    change ∀ k, x n i k ∈ Set.Icc (0 : ℝ) 1
    rw [Fin.forall_fin_two]
    have h := design_fraction_mem i
    exact ⟨h, ⟨sub_nonneg.mpr h.2, sub_le_self _ h.1⟩⟩

/-- W2: the one-coordinate corollary for the identity at smoothness `1/2`. -/
theorem cor_chebyshev_witness_one :
    let α : Fin 1 → ℝ := fun _ => 1 / 2
    let f₀ : (Fin 1 → ℝ) → ℝ := fun y => y 0
    let x : (n : ℕ) → Fin n → Fin 1 → ℝ := fun n i _ => (i : ℝ) / n
    let b := betaExp α
    ∃ CJ : Fin 1 → ℝ, 0 < chebCapp (by decide) α (fun _ => 1) CJ 1 ∧
      ∃ c5 : ℝ, 0 ≤ c5 ∧
        CorConclusion α (chebJ b) (chebX b x) (fun n i => f₀ (x n i)) 1
          (fun n => horseshoePDF (corTau 1 n (chebJ b n))) 1
          (chebCapp (by decide) α (fun _ => 1) CJ 1) (1 / 2)
          (Aconst (Real.sqrt 2 ^ 1) (1 / 2) 1 (1 / 2) 1 c5) := by
  intro α f₀ x
  have hα : ∀ k, 0 < α k := fun _ => by norm_num [α]
  have hα1 : ∀ k, α k < 1 := fun _ => by norm_num [α]
  have hf : SecHolderBall α 1 f₀ := by
    refine ⟨(continuous_apply 0).continuousOn, ?_⟩
    intro y _ k
    obtain rfl : k = 0 := Subsingleton.elim _ _
    change HolderBallIcc (1 / 2) 1 (fun t => Function.update y 0 t 0)
    simpa only [Function.update_self, one_mul] using
      holderBallIcc_linear (α := 1 / 2) (a := 1) (by norm_num) (by norm_num) (by norm_num : |(1 : ℝ)| ≤ 1)
  simpa only [Nat.cast_one, one_mul] using
    cheb_holder_witness (by decide) hα hα1 hf (x := x) (fun _ i _ => design_fraction_mem i)

end LargePrior
