import LargePrior.Spec

/-!
# Sanity checks of the definitions in `LargePrior/Spec.lean`

Small lemmas that would expose a wrongly written definition: explicit values of the knot vector,
low-order B-splines, Fourier atoms, the empirical norm, the likelihood ratio, the half-Cauchy and
horseshoe densities, and the fact that the posterior does not depend on the reference point of the
likelihood ratio (so that it is the Bayes posterior).
Blueprint: Remark `rem:bspl-sanity` (partB.tex) and Remark `rem:Dfinite` (LargePrior_blueprint.tex).
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal Matrix

namespace LargePrior

/-! ## Knots and B-splines -/

lemma knot_sanity :
    knot 3 2 0 = 0 ∧ knot 3 2 2 = 0 ∧ knot 3 2 3 = 1 / 2 ∧ knot 3 2 4 = 1 ∧ knot 3 2 6 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [knot]

private lemma knot_q2_K1 :
    knot 2 1 0 = 0 ∧ knot 2 1 1 = 0 ∧ knot 2 1 2 = 1 ∧ knot 2 1 3 = 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num [knot]

private lemma bspl_one (q K i : ℕ) (x : ℝ) :
    bspl q K 1 i x = if (knot q K i ≤ x ∧ x < knot q K (i + 1)) ∨
          (x = 1 ∧ knot q K i < 1 ∧ knot q K (i + 1) = 1) then 1 else 0 := rfl

private lemma bspl_two (q K i : ℕ) (x : ℝ) :
    bspl q K 2 i x = (x - knot q K i) / (knot q K (i + 1) - knot q K i) * bspl q K 1 i x +
      (knot q K (i + 2) - x) / (knot q K (i + 2) - knot q K (i + 1)) * bspl q K 1 (i + 1) x := rfl

lemma bspline_q2_K1 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    bspline 2 1 0 x = 1 - x ∧ bspline 2 1 1 x = x := by
  obtain ⟨k0, k1, k2, k3⟩ := knot_q2_K1
  obtain ⟨hx0, hx1⟩ := hx
  have h1 : bspl 2 1 1 1 x = 1 := by
    rw [bspl_one]
    rcases hx1.lt_or_eq with h | h
    · simp [k1, k2, hx0, h]
    · simp [k1, k2, h]
  have h2 : bspl 2 1 1 2 x = 0 := by
    rw [bspl_one]; simp [k2, k3]
  constructor
  · rw [bspline, bspl_two]
    simp [k0, k1, k2, h1]
  · rw [bspline, bspl_two]
    simp [k1, k2, k3, h1, h2]

private lemma bspl_one_eq_one {q K i : ℕ} {x a b : ℝ} (ha : knot q K i = a)
    (hb : knot q K (i + 1) = b) (h : (a ≤ x ∧ x < b) ∨ (x = 1 ∧ a < 1 ∧ b = 1)) :
    bspl q K 1 i x = 1 := by
  rw [bspl_one, ha, hb]; exact ite_eq_left h

private lemma bspl_one_eq_zero {q K i : ℕ} {x a b : ℝ} (ha : knot q K i = a)
    (hb : knot q K (i + 1) = b) (h : ¬((a ≤ x ∧ x < b) ∨ (x = 1 ∧ a < 1 ∧ b = 1))) :
    bspl q K 1 i x = 0 := by
  rw [bspl_one, ha, hb]; exact ite_eq_right h

private lemma knot_q1_K2 : knot 1 2 0 = 0 ∧ knot 1 2 1 = 1 / 2 ∧ knot 1 2 2 = 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num [knot]

lemma bspline_q1_K2 (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 1) :
    bspline 1 2 0 x = (if x < 1 / 2 then 1 else 0) ∧
      bspline 1 2 1 x = (if 1 / 2 ≤ x then 1 else 0) := by
  obtain ⟨k0, k1, k2⟩ := knot_q1_K2
  obtain ⟨hx0, hx1⟩ := hx
  constructor
  · rw [bspline]
    by_cases h : x < 1 / 2
    · rw [bspl_one_eq_one k0 k1 (Or.inl ⟨hx0, h⟩), ite_eq_left h]
    · rw [bspl_one_eq_zero k0 k1 ?_, ite_eq_right h]
      rintro (⟨_, h2⟩ | ⟨_, _, h3⟩)
      · exact h h2
      · norm_num at h3
  · rw [bspline]
    by_cases h : 1 / 2 ≤ x
    · rw [ite_eq_left h]
      rcases hx1.lt_or_eq with h' | h'
      · exact bspl_one_eq_one k1 k2 (Or.inl ⟨h, h'⟩)
      · exact bspl_one_eq_one k1 k2 (Or.inr ⟨h', by norm_num, rfl⟩)
    · rw [bspl_one_eq_zero k1 k2 ?_, ite_eq_right h]
      rintro (⟨h2, _⟩ | ⟨h3, _, _⟩)
      · exact h h2
      · exact h (by rw [h3]; norm_num)

private lemma knot_q2_K2 :
    knot 2 2 0 = 0 ∧ knot 2 2 1 = 0 ∧ knot 2 2 2 = 1 / 2 ∧ knot 2 2 3 = 1 ∧ knot 2 2 4 = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [knot]

lemma bspline_q2_K2_mid :
    bspline 2 2 1 (1 / 2) = 1 ∧ bspline 2 2 0 (1 / 2) = 0 ∧ bspline 2 2 2 (1 / 2) = 0 := by
  obtain ⟨k0, k1, k2, k3, k4⟩ := knot_q2_K2
  have b0 : bspl 2 2 1 0 (1 / 2) = 0 :=
    bspl_one_eq_zero k0 k1 (by rintro (⟨_, h⟩ | ⟨h, _⟩) <;> norm_num at h)
  have b1 : bspl 2 2 1 1 (1 / 2) = 0 :=
    bspl_one_eq_zero k1 k2 (by rintro (⟨_, h⟩ | ⟨h, _⟩) <;> norm_num at h)
  have b2 : bspl 2 2 1 2 (1 / 2) = 1 :=
    bspl_one_eq_one k2 k3 (Or.inl ⟨le_rfl, by norm_num⟩)
  have b3 : bspl 2 2 1 3 (1 / 2) = 0 :=
    bspl_one_eq_zero k3 k4 (by rintro (⟨h, _⟩ | ⟨h, _⟩) <;> norm_num at h)
  refine ⟨?_, ?_, ?_⟩
  · rw [bspline, bspl_two]
    simp only [Nat.reduceAdd, k1, k2, k3, b1, b2]
    norm_num
  · rw [bspline, bspl_two]
    simp only [Nat.reduceAdd, k0, k1, k2, b0, b1]
    norm_num
  · rw [bspline, bspl_two]
    simp only [Nat.reduceAdd, k2, k3, k4, b2, b3]
    norm_num

/-! ## Fourier atoms -/

lemma fourierAtom_sanity (x : ℝ) :
    fourierAtom 0 x = 1 ∧
    fourierAtom 1 x = Real.sqrt 2 * Real.cos (2 * Real.pi * x) ∧
    fourierAtom 2 x = Real.sqrt 2 * Real.sin (2 * Real.pi * x) ∧
    fourierAtom 3 x = Real.sqrt 2 * Real.cos (2 * Real.pi * 2 * x) ∧
    fourierAtom 4 x = Real.sqrt 2 * Real.sin (2 * Real.pi * 2 * x) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [fourierAtom]

/-! ## Empirical norm and counting -/

lemma empNorm_const {n : ℕ} (hn : 0 < n) (c : ℝ) : empNorm (fun _ : Fin n => c) = |c| := by
  have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  rw [empNorm]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_div_cancel_left₀ _ hn', Real.sqrt_sq_eq_abs]

lemma numLarge_sanity : numLarge (J := 3) 1 ![0, 2, -3] = 2 := by
  have h : (univ.filter (fun j : Fin 3 => (1 : ℝ) < |(![0, 2, -3] : Fin 3 → ℝ) j|)) = {1, 2} := by
    ext j
    fin_cases j <;> norm_num [abs_of_neg]
  rw [numLarge, h]
  rfl

/-! ## Likelihood ratio -/

lemma likRatio_self (σ : ℝ) {n : ℕ} (f₀ y : Fin n → ℝ) : likRatio σ f₀ f₀ y = 1 := by
  simp [likRatio]

/-! ## Half-Cauchy and horseshoe densities -/

lemma halfCauchyPDF_one : halfCauchyPDF 1 = 1 / Real.pi := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  simp only [halfCauchyPDF, ite_eq_left one_pos]
  field_simp
  norm_num

lemma horseshoePDF_neg (τ t : ℝ) : horseshoePDF τ (-t) = horseshoePDF τ t := by
  simp [horseshoePDF, gaussianPDFReal]

/-! ## Change of reference point and the posterior -/

lemma likRatio_ref (σ : ℝ) (hσ : 0 < σ) {n : ℕ} (f₀ f₁ g y : Fin n → ℝ) :
    likRatio σ f₀ g y = likRatio σ f₁ g y * likRatio σ f₀ f₁ y := by
  have h : ∀ u v : Fin n → ℝ,
      (∑ i, (y i - u i) * (v i - u i)) / σ ^ 2 - (∑ i, (v i - u i) ^ 2) / (2 * σ ^ 2) =
        ∑ i, ((y i - u i) ^ 2 - (y i - v i) ^ 2) / (2 * σ ^ 2) := by
    intro u v
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    field_simp
    ring
  unfold likRatio
  rw [← Real.exp_add, h, h, h, ← Finset.sum_add_distrib]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

lemma posterior_ref_invariant {σ : ℝ} (hσ : 0 < σ) {n J : ℕ} (X : Matrix (Fin n) (Fin J) ℝ)
    (f₀ f₁ : Fin n → ℝ) (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri]
    (y : Fin n → ℝ) : posterior σ X f₀ pri y = posterior σ X f₁ pri y := by
  set a : ℝ≥0∞ := ENNReal.ofReal (likRatio σ f₀ f₁ y) with ha
  have ha0 : a ≠ 0 := by
    rw [ha, Ne, ENNReal.ofReal_eq_zero, not_le]
    exact Real.exp_pos _
  have hat : a ≠ ∞ := ENNReal.ofReal_ne_top
  have hdens : ∀ θ : Fin J → ℝ, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) =
      a * ENNReal.ofReal (likRatio σ f₁ (X *ᵥ θ) y) := by
    intro θ
    have hL : 0 ≤ likRatio σ f₁ (X *ᵥ θ) y := (Real.exp_pos _).le
    rw [likRatio_ref σ hσ f₀ f₁ (X *ᵥ θ) y, ENNReal.ofReal_mul hL, mul_comm]
  have hev : evidence σ X f₀ pri y = a * evidence σ X f₁ pri y := by
    unfold evidence
    rw [← lintegral_const_mul' a _ hat]
    exact lintegral_congr hdens
  have hwd : pri.withDensity (fun θ => ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y)) =
      a • pri.withDensity (fun θ => ENNReal.ofReal (likRatio σ f₁ (X *ᵥ θ) y)) := by
    rw [← withDensity_smul' a _ hat]
    congr 1
    funext θ
    exact hdens θ
  unfold posterior
  rw [hwd, hev, ENNReal.mul_inv (Or.inl ha0) (Or.inl hat), smul_smul]
  congr 1
  rw [mul_comm a⁻¹, mul_assoc, ENNReal.inv_mul_cancel ha0 hat, mul_one]

end LargePrior
