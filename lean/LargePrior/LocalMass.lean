import LargePrior.Posterior

/-!
# Lemma 1: local prior mass (blueprint `lem:local-mass`)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

variable {n J : ℕ}

/-- `B(r) = {θ : ‖Xθ − f₀‖_{2,n} ≤ r}`. -/
def localBall (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (r : ℝ) : Set (Fin J → ℝ) :=
  {θ | empNorm (X *ᵥ θ - f₀) ≤ r}

lemma measurableSet_localBall (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (r : ℝ) :
    MeasurableSet (localBall X f₀ r) := by
  have hc : Continuous fun θ : Fin J → ℝ => empNorm (X *ᵥ θ - f₀) :=
    continuous_empNorm.comp ((continuous_const.matrix_mulVec continuous_id).sub continuous_const)
  exact (isClosed_le hc continuous_const).measurableSet

/-! ### Step 1: an `ℓ₁` coefficient ball lies inside the local ball -/

private lemma mem_localBall_of_l1 {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ} {K εt η : ℝ}
    (hX : BasisBound X K) (hK : 0 ≤ K) {θ₀ θ : Fin J → ℝ} (h0 : empNorm (f₀ - X *ᵥ θ₀) ≤ εt)
    (h : ∑ j, |θ j - θ₀ j| ≤ (1 + 2 * η) * εt) :
    θ ∈ localBall X f₀ (Ltil K η * εt) := by
  show empNorm (X *ᵥ θ - f₀) ≤ Ltil K η * εt
  have h1 := empNorm_sub_le (X *ᵥ θ) (X *ᵥ θ₀) f₀
  have h2 : empNorm (X *ᵥ θ - X *ᵥ θ₀) ≤ K * ∑ j, |θ j - θ₀ j| := by
    rw [← Matrix.mulVec_sub]
    simpa using empNorm_mulVec_le hX (θ - θ₀)
  rw [empNorm_sub_comm (X *ᵥ θ₀)] at h1
  have h3 : K * ∑ j, |θ j - θ₀ j| ≤ K * ((1 + 2 * η) * εt) := mul_le_mul_of_nonneg_left h hK
  have h4 : Ltil K η * εt = εt + K * ((1 + 2 * η) * εt) := by unfold Ltil; ring
  linarith

/-- Splitting the `ℓ₁` distance into the active block `S` and the inactive block `Sᶜ`. -/
private lemma l1_le_of_blocks {θ₀ θ : Fin J → ℝ} {S : Finset (Fin J)} {εt δ η : ℝ}
    (hJδ : (J : ℝ) * δ ≤ εt) (hθ₀ : ∀ j ∉ S, |θ₀ j| ≤ δ)
    (hS : ∑ j ∈ S, |θ j - θ₀ j| ≤ η * εt + S.card * δ)
    (hSc : ∑ j ∈ Sᶜ, |θ j| ≤ η * εt) :
    ∑ j, |θ j - θ₀ j| ≤ (1 + 2 * η) * εt := by
  rw [← Finset.sum_add_sum_compl S]
  have h1 : ∑ j ∈ Sᶜ, |θ j - θ₀ j| ≤ ∑ j ∈ Sᶜ, (|θ j| + δ) := Finset.sum_le_sum fun j hj => by
    have := hθ₀ j (Finset.mem_compl.1 hj)
    have := abs_sub (θ j) (θ₀ j)
    linarith
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul] at h1
  have hc : (S.card : ℝ) * δ + (Sᶜ.card : ℝ) * δ = J * δ := by
    rw [← add_mul, ← Nat.cast_add, Finset.card_add_card_compl, Fintype.card_fin]
  linarith

/-! ### Step 3: block independence under the product prior -/

/-- The prior of a box on the active coordinates. -/
private lemma prior_box {pdf : ℝ → ℝ} (hpdf : IsProbDensity pdf) (S : Finset (Fin J))
    (A : Fin J → Set ℝ) :
    prior J pdf {θ | ∀ j ∈ S, θ j ∈ A j} = ∏ j ∈ S, coordPrior pdf (A j) := by
  have := isProbabilityMeasure_coordPrior hpdf
  have hset : {θ : Fin J → ℝ | ∀ j ∈ S, θ j ∈ A j} =
      Set.univ.pi fun j => if j ∈ S then A j else Set.univ := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
    constructor
    · intro h j
      split_ifs with hj
      · exact h j hj
      · trivial
    · intro h j hj
      simpa [hj] using h j
  rw [hset, prior, Measure.pi_pi]
  simp [apply_ite, Finset.prod_ite_mem]

/-- The active-box event and the inactive-sum event are independent under the prior. -/
private lemma prior_box_inter {pdf : ℝ → ℝ} (hpdf : IsProbDensity pdf) (S : Finset (Fin J))
    {A : Fin J → Set ℝ} (hA : ∀ j, MeasurableSet (A j)) (c : ℝ) :
    prior J pdf ({θ | ∀ j ∈ S, θ j ∈ A j} ∩ {θ | ∑ j ∈ Sᶜ, |θ j| ≤ c}) =
      (∏ j ∈ S, coordPrior pdf (A j)) * prior J pdf {θ | ∑ j ∈ Sᶜ, |θ j| ≤ c} := by
  have := isProbabilityMeasure_coordPrior hpdf
  have hind : iIndepFun (fun (j : Fin J) (θ : Fin J → ℝ) => θ j) (prior J pdf) :=
    iIndepFun_pi (X := fun _ => id) (fun _ => measurable_id.aemeasurable)
  have h2 := hind.indepFun_finset S Sᶜ disjoint_compl_right (fun j => measurable_pi_apply j)
  have hbox : {θ : Fin J → ℝ | ∀ j ∈ S, θ j ∈ A j} =
      (fun θ (i : S) => θ i) ⁻¹' (Set.univ.pi fun i : S => A i) := by
    ext θ
    simp
  have hsum : {θ : Fin J → ℝ | ∑ j ∈ Sᶜ, |θ j| ≤ c} =
      (fun θ (i : (Sᶜ : Finset (Fin J))) => θ i) ⁻¹' {u | ∑ i, |u i| ≤ c} := by
    ext θ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rw [Finset.sum_coe_sort Sᶜ (fun j => |θ j|)]
  have hmeas : MeasurableSet {u : (Sᶜ : Finset (Fin J)) → ℝ | ∑ i, |u i| ≤ c} :=
    measurableSet_le (Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).abs)
      measurable_const
  rw [← prior_box hpdf S A, hbox, hsum]
  exact (indepFun_iff_measure_inter_preimage_eq_mul.1 h2) _ _
    (MeasurableSet.univ_pi fun i : S => hA i) hmeas

/-- Assembly: if every point of the active box is `ℓ₁`-close on `S`, the prior of the local ball
is at least (prior of the box) × (prior of the inactive event). -/
private lemma prior_localBall_ge {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ} {pdf : ℝ → ℝ}
    {εt δ K η : ℝ} (hpdf : IsProbDensity pdf) (hK : 0 ≤ K) (hX : BasisBound X K)
    (hJδ : (J : ℝ) * δ ≤ εt) {θ₀ : Fin J → ℝ} {S : Finset (Fin J)}
    (h0 : empNorm (f₀ - X *ᵥ θ₀) ≤ εt) (hθ₀ : ∀ j ∉ S, |θ₀ j| ≤ δ)
    {A : Fin J → Set ℝ} (hA : ∀ j, MeasurableSet (A j))
    (hin : ∀ θ : Fin J → ℝ, (∀ j ∈ S, θ j ∈ A j) →
      ∑ j ∈ S, |θ j - θ₀ j| ≤ η * εt + S.card * δ) :
    (∏ j ∈ S, coordPrior pdf (A j)) * prior J pdf {θ | ∑ j ∈ Sᶜ, |θ j| ≤ η * εt} ≤
      prior J pdf (localBall X f₀ (Ltil K η * εt)) := by
  rw [← prior_box_inter hpdf S hA]
  refine measure_mono fun θ hθ => ?_
  obtain ⟨h1, h2⟩ := hθ
  exact mem_localBall_of_l1 hX hK h0 (l1_le_of_blocks hJδ hθ₀ (hin θ h1) h2)

/-! ### Step 4: case `E ≥ h` -/

private lemma interval_facts {x E h t : ℝ} (hx : |x| ≤ E) (hhE : h ≤ E) (hh : 0 ≤ h)
    (ht : t ∈ Set.Icc (if 0 < x then x - h else x) ((if 0 < x then x - h else x) + h)) :
    |t| ≤ E ∧ |t - x| ≤ h := by
  rw [abs_le] at hx
  split_ifs at ht with hpos <;> obtain ⟨h1, h2⟩ := ht <;>
    exact ⟨abs_le.2 ⟨by linarith, by linarith⟩, abs_le.2 ⟨by linarith, by linarith⟩⟩

private lemma coordPrior_Icc_ge {pdf : ℝ → ℝ} {E πlow l h : ℝ}
    (hlow : ∀ᵐ t ∂volume, |t| ≤ E → πlow ≤ pdf t) (hsub : ∀ t ∈ Set.Icc l (l + h), |t| ≤ E)
    (hh : 0 ≤ h) :
    ENNReal.ofReal (h * πlow) ≤ coordPrior pdf (Set.Icc l (l + h)) := by
  rw [coordPrior, withDensity_apply _ measurableSet_Icc]
  have hae : ∀ᵐ t ∂(volume.restrict (Set.Icc l (l + h))),
      ENNReal.ofReal πlow ≤ ENNReal.ofReal (pdf t) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    filter_upwards [hlow] with t ht hmem
    exact ENNReal.ofReal_le_ofReal (ht (hsub t hmem))
  calc ENNReal.ofReal (h * πlow) = ∫⁻ _ in Set.Icc l (l + h), ENNReal.ofReal πlow := by
        rw [setLIntegral_const, Real.volume_Icc, add_sub_cancel_left, ENNReal.ofReal_mul hh,
          mul_comm]
    _ ≤ _ := lintegral_mono_ae hae

private lemma case1_real {a n : ℕ} {η εt πlow c5 : ℝ} (ha : 1 ≤ a) (hη : 0 < η) (hεt : 0 < εt)
    (e1 : εt ≤ η) (hπ : 0 < πlow)
    (hW : (a : ℝ) * max 0 (Real.log a + 2 * Real.log (1 / εt) - Real.log πlow) ≤
      c5 * n * εt ^ 2) :
    Real.exp (-(c5 * n * εt ^ 2)) ≤ (η * εt / a * πlow) ^ a := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb : 0 < η * εt / a * πlow := by positivity
  rw [← Real.exp_log (pow_pos hb a), Real.exp_le_exp, Real.log_pow,
    Real.log_mul (by positivity) hπ.ne', Real.log_div (by positivity) ha0.ne',
    Real.log_mul hη.ne' hεt.ne']
  have h1 : Real.log (εt * εt) ≤ Real.log (η * εt) :=
    Real.log_le_log (by positivity) (mul_le_mul_of_nonneg_right e1 hεt.le)
  rw [Real.log_mul hεt.ne' hεt.ne', Real.log_mul hη.ne' hεt.ne'] at h1
  have h2 : Real.log (1 / εt) = -Real.log εt := by rw [one_div, Real.log_inv]
  have h4 : Real.log a - (Real.log η + Real.log εt) - Real.log πlow ≤
      max 0 (Real.log a + 2 * Real.log (1 / εt) - Real.log πlow) :=
    le_trans (by rw [h2]; linarith) (le_max_right _ _)
  have h5 := mul_le_mul_of_nonneg_left h4 ha0.le
  linarith

private lemma case1_mass {pdf : ℝ → ℝ} {E εt c5 η : ℝ} {a : ℕ} {S : Finset (Fin J)}
    {θ₀ : Fin J → ℝ} (h5 : WG5 pdf E εt c5 a n) (ha1 : 1 ≤ a) (hη : 0 < η) (hεt : 0 < εt)
    (e1 : εt ≤ η) (hcard : S.card = a) (hθE : ∀ j, |θ₀ j| ≤ E)
    (hhE : η * εt / a ≤ E) :
    ENNReal.ofReal (Real.exp (-(c5 * n * εt ^ 2))) ≤
      ∏ j ∈ S, coordPrior pdf (Set.Icc (if 0 < θ₀ j then θ₀ j - η * εt / a else θ₀ j)
        ((if 0 < θ₀ j then θ₀ j - η * εt / a else θ₀ j) + η * εt / a)) := by
  obtain ⟨πlow, hπ, hlow, hW⟩ := h5
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  have hh : 0 ≤ η * εt / a := by positivity
  calc ENNReal.ofReal (Real.exp (-(c5 * n * εt ^ 2)))
      ≤ ENNReal.ofReal ((η * εt / a * πlow) ^ a) :=
        ENNReal.ofReal_le_ofReal (case1_real ha1 hη hεt e1 hπ hW)
    _ = ∏ _j ∈ S, ENNReal.ofReal (η * εt / a * πlow) := by
        rw [Finset.prod_const, hcard, ENNReal.ofReal_pow (by positivity)]
    _ ≤ _ := Finset.prod_le_prod fun j _ =>
        coordPrior_Icc_ge hlow (fun t ht => (interval_facts (hθE j) hhE hh ht).1) hh

/-! ### Step 5: case `E < h` -/

private lemma case2_real {J a : ℕ} {μ : ℝ} (hJ : 2 ≤ J) (haJ : a ≤ J)
    (e2 : 2 ≤ (J : ℝ) ^ μ) :
    (a : ℝ) * (J : ℝ) ^ (-(1 + μ)) ≤ 1 / 2 := by
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have haJ' : (a : ℝ) ≤ J := by exact_mod_cast haJ
  have hsplit : (J : ℝ) ^ (-(1 + μ)) = (J : ℝ)⁻¹ * ((J : ℝ) ^ μ)⁻¹ := by
    rw [show -(1 + μ) = (-1 : ℝ) + -μ by ring, Real.rpow_add hJ0, Real.rpow_neg_one,
      Real.rpow_neg hJ0.le]
  have hpow : 0 < (J : ℝ) ^ μ := Real.rpow_pos_of_pos hJ0 μ
  have h1 : (a : ℝ) / J ≤ 1 := (div_le_one hJ0).2 haJ'
  have h2 : ((J : ℝ) ^ μ)⁻¹ ≤ 1 / 2 := by
    rw [inv_eq_one_div]
    exact one_div_le_one_div_of_le (by norm_num) e2
  have h4 : 0 ≤ ((J : ℝ) ^ μ)⁻¹ := by positivity
  calc (a : ℝ) * (J : ℝ) ^ (-(1 + μ)) = (a / J) * ((J : ℝ) ^ μ)⁻¹ := by
        rw [hsplit, div_eq_mul_inv, mul_assoc]
    _ ≤ 1 * (1 / 2) := mul_le_mul h1 h2 h4 zero_le_one
    _ = 1 / 2 := one_mul _

private lemma case2_mass {pdf : ℝ → ℝ} (hpdf : IsProbDensity pdf) {δ μ : ℝ} {a : ℕ}
    {S : Finset (Fin J)} (hJ : 2 ≤ J) (ha1 : 1 ≤ a) (haJ : a ≤ J) (hcard : S.card = a)
    (h3 : WG3 pdf δ μ J) (e2 : 2 ≤ (J : ℝ) ^ μ) :
    ENNReal.ofReal (1 / 2) ≤ ∏ _j ∈ S, coordPrior pdf (Set.Icc (-δ) δ) := by
  have := isProbabilityMeasure_coordPrior hpdf
  set q : ℝ := (J : ℝ) ^ (-(1 + μ)) with hq_def
  have hq0 : 0 ≤ q := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have haq := case2_real hJ haJ e2
  rw [← hq_def] at haq
  have ha0 : (1 : ℝ) ≤ a := by exact_mod_cast ha1
  have hq1 : q ≤ 1 / 2 := by nlinarith
  have hcompl : (Set.Icc (-δ) δ)ᶜ = {t : ℝ | δ < |t|} := by
    ext t
    simp [abs_le.symm, not_le]
  have hsingle : ENNReal.ofReal (1 - q) ≤ coordPrior pdf (Set.Icc (-δ) δ) := by
    rw [ENNReal.ofReal_sub _ hq0, ENNReal.ofReal_one, tsub_le_iff_right]
    calc (1 : ℝ≥0∞) = coordPrior pdf (Set.Icc (-δ) δ) + coordPrior pdf (Set.Icc (-δ) δ)ᶜ := by
          rw [measure_add_measure_compl measurableSet_Icc, measure_univ]
      _ ≤ _ := by
          rw [hcompl]
          exact add_le_add le_rfl h3
  have hbern : 1 / 2 ≤ (1 - q) ^ a := by
    have := one_add_mul_le_pow (a := -q) (by linarith) a
    rw [← sub_eq_add_neg] at this
    linarith
  calc ENNReal.ofReal (1 / 2) ≤ ENNReal.ofReal ((1 - q) ^ a) := ENNReal.ofReal_le_ofReal hbern
    _ = ∏ _j ∈ S, ENNReal.ofReal (1 - q) := by
        rw [Finset.prod_const, hcard, ENNReal.ofReal_pow (by linarith)]
    _ ≤ _ := Finset.prod_le_prod fun _ _ => hsingle

/-! ### Step 6: assembly -/

/-- **Lemma 1** (local prior mass): `Π(B(L̃ ε̃)) ≥ exp(−C_Π n ε̃²)`. -/
theorem local_mass {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ} {pdf : ℝ → ℝ}
    {εt δ E K η μ c4 c5 : ℝ} {a : ℕ} (hJ : 2 ≤ J) (hpdf : IsProbDensity pdf)
    (hεt : 0 < εt) (hδ : 0 < δ) (hE : 0 < E) (ha1 : 1 ≤ a) (haJ : a ≤ J) (hK : 0 < K)
    (hη : 0 < η) (hμ : 0 < μ) (hc4 : 0 ≤ c4) (hc5 : 0 ≤ c5) (hδεt : δ ≤ εt / J)
    (hX : BasisBound X K) {θ₀ : Fin J → ℝ} {S : Finset (Fin J)}
    (hA2 : SparseApprox X f₀ εt δ E a θ₀ S) (h4 : WG4 pdf J S η εt c4 n)
    (h3 : WG3 pdf δ μ J) (h5 : WG5 pdf E εt c5 a n)
    (e1 : εt ≤ η) (e2 : 2 ≤ (J : ℝ) ^ μ) (e3 : Real.log 2 ≤ n * εt ^ 2) :
    ENNReal.ofReal (Real.exp (-(CPi c4 c5 * n * εt ^ 2))) ≤
      prior J pdf (localBall X f₀ (Ltil K η * εt)) := by
  -- `hE`, `hμ`, `hc4` are part of the frozen statement and not needed by the proof.
  have _ := hE
  have _ := hμ
  have _ := hc4
  obtain ⟨h0, -, hθE, hcard, hθ₀⟩ := hA2
  have hJ0 : (0 : ℝ) < J := by exact_mod_cast (show 0 < J by omega)
  have hJδ : (J : ℝ) * δ ≤ εt := by
    rw [mul_comm]; exact (le_div_iff₀ hJ0).1 hδεt
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha1
  have hx : 0 ≤ (n : ℝ) * εt ^ 2 := by positivity
  set h : ℝ := η * εt / a with hh_def
  have hah : (a : ℝ) * h = η * εt := by rw [hh_def]; field_simp
  have hh0 : 0 ≤ h := by positivity
  rcases le_or_gt h E with hhE | hhE
  · -- Case 1: `E ≥ h`
    set A : Fin J → Set ℝ := fun j => Set.Icc (if 0 < θ₀ j then θ₀ j - h else θ₀ j)
      ((if 0 < θ₀ j then θ₀ j - h else θ₀ j) + h) with hA_def
    have hin : ∀ θ : Fin J → ℝ, (∀ j ∈ S, θ j ∈ A j) →
        ∑ j ∈ S, |θ j - θ₀ j| ≤ η * εt + S.card * δ := by
      intro θ hθ
      have hsum : ∑ j ∈ S, |θ j - θ₀ j| ≤ ∑ _j ∈ S, h :=
        Finset.sum_le_sum fun j hj => (interval_facts (hθE j) hhE hh0 (hθ j hj)).2
      rw [Finset.sum_const, nsmul_eq_mul, hcard, hah] at hsum
      have : (0 : ℝ) ≤ S.card * δ := by positivity
      linarith
    have hmain := prior_localBall_ge (A := A) hpdf hK.le hX hJδ h0 hθ₀
      (fun _ => measurableSet_Icc) hin
    have hm1 := case1_mass (S := S) (θ₀ := θ₀) h5 ha1 hη hεt e1 hcard hθE hhE
    refine le_trans ?_ hmain
    calc ENNReal.ofReal (Real.exp (-(CPi c4 c5 * n * εt ^ 2)))
        ≤ ENNReal.ofReal (Real.exp (-(c5 * n * εt ^ 2)) * Real.exp (-(c4 * n * εt ^ 2))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [← Real.exp_add, Real.exp_le_exp]
          unfold CPi
          nlinarith
      _ = ENNReal.ofReal (Real.exp (-(c5 * n * εt ^ 2))) *
            ENNReal.ofReal (Real.exp (-(c4 * n * εt ^ 2))) :=
          ENNReal.ofReal_mul (Real.exp_pos _).le
      _ ≤ _ := mul_le_mul' hm1 h4
  · -- Case 2: `E < h`
    have hin : ∀ θ : Fin J → ℝ, (∀ j ∈ S, θ j ∈ (fun _ : Fin J => Set.Icc (-δ) δ) j) →
        ∑ j ∈ S, |θ j - θ₀ j| ≤ η * εt + S.card * δ := by
      intro θ hθ
      have hsum : ∑ j ∈ S, |θ j - θ₀ j| ≤ ∑ _j ∈ S, (δ + E) :=
        Finset.sum_le_sum fun j hj => by
          have h1 : |θ j| ≤ δ := abs_le.2 (hθ j hj)
          have h2 := abs_sub (θ j) (θ₀ j)
          have h3 := hθE j
          linarith
      rw [Finset.sum_const, nsmul_eq_mul, hcard] at hsum
      rw [hcard]
      have : (a : ℝ) * E ≤ a * h := mul_le_mul_of_nonneg_left hhE.le ha0.le
      nlinarith
    have hmain := prior_localBall_ge (A := fun _ => Set.Icc (-δ) δ) hpdf hK.le hX hJδ h0 hθ₀
      (fun _ => measurableSet_Icc) hin
    have hm2 := case2_mass (S := S) hpdf hJ ha1 haJ hcard h3 e2
    refine le_trans ?_ hmain
    have hexp : Real.exp (-(n * εt ^ 2)) ≤ 1 / 2 := by
      calc Real.exp (-(n * εt ^ 2)) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
        _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num), one_div]
    calc ENNReal.ofReal (Real.exp (-(CPi c4 c5 * n * εt ^ 2)))
        ≤ ENNReal.ofReal (1 / 2 * Real.exp (-(c4 * n * εt ^ 2))) := by
          refine ENNReal.ofReal_le_ofReal ?_
          have hs : Real.exp (-(CPi c4 c5 * n * εt ^ 2)) ≤
              Real.exp (-(n * εt ^ 2)) * Real.exp (-(c4 * n * εt ^ 2)) := by
            rw [← Real.exp_add, Real.exp_le_exp]
            unfold CPi
            nlinarith
          have hpos := (Real.exp_pos (-(c4 * n * εt ^ 2))).le
          nlinarith
      _ = ENNReal.ofReal (1 / 2) * ENNReal.ofReal (Real.exp (-(c4 * n * εt ^ 2))) :=
          ENNReal.ofReal_mul (by norm_num)
      _ ≤ _ := mul_le_mul' hm2 h4

end LargePrior
