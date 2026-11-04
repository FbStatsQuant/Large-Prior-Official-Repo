import LargePrior.Tests
import LargePrior.Evidence
import LargePrior.Sieve

/-!
# Theorem 1 at a fixed sample size (blueprint `thm:master`)

The proof assembles Lemmas 1–4 through the posterior decomposition.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

/-- The sieve term after division by the evidence bound:
`e^{C₁ n ε̃²} e^{−μ A n ε²} ≤ e^{−n ε²}`. -/
lemma master_sieve_real {C μA nεt2 nε2 : ℝ} (hC : 0 ≤ C) (hle : nεt2 ≤ nε2)
    (hμA : C + 1 ≤ μA) (hnε2 : 0 ≤ nε2) :
    (Real.exp (-(C * nεt2)))⁻¹ * Real.exp (-(μA * nε2)) ≤ Real.exp (-nε2) := by
  rw [← Real.exp_neg, neg_neg, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  nlinarith [mul_le_mul_of_nonneg_left hle hC, mul_le_mul_of_nonneg_right hμA hnε2]

/-- The test term after division by the evidence bound:
`e^{C₁ n ε̃²} e^{−M² n ε²/(64σ²)} ≤ e^{−n ε²}` when `M² ≥ 64σ²(C₁+1)`. -/
lemma master_test_real {C σ M nεt2 nε2 : ℝ} (hC : 0 ≤ C) (hσ : 0 < σ) (hle : nεt2 ≤ nε2)
    (hnε2 : 0 ≤ nε2) (hM : 64 * σ ^ 2 * (C + 1) ≤ M ^ 2) :
    (Real.exp (-(C * nεt2)))⁻¹ * Real.exp (-(M ^ 2 * nε2 / (64 * σ ^ 2))) ≤
      Real.exp (-nε2) := by
  have hσ2 : 0 < 64 * σ ^ 2 := by positivity
  have h1 : C + 1 ≤ M ^ 2 / (64 * σ ^ 2) := by
    rw [le_div_iff₀ hσ2]; linarith
  rw [show M ^ 2 * nε2 / (64 * σ ^ 2) = M ^ 2 / (64 * σ ^ 2) * nε2 by ring]
  exact master_sieve_real hC hle h1 hnε2

private lemma ofReal_combine {a b c d e : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c)
    (hd : 0 ≤ d) (he : 0 ≤ e) :
    ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c * (ENNReal.ofReal d + ENNReal.ofReal e) =
      ENNReal.ofReal (a + b + c * (d + e)) := by
  rw [← ENNReal.ofReal_add hd he, ← ENNReal.ofReal_mul hc, ← ENNReal.ofReal_add ha hb,
    ← ENNReal.ofReal_add (add_nonneg ha hb) (mul_nonneg hc (add_nonneg hd he))]

/-- **Step: arithmetic for the tests.** With `m = A s_n`, `n ε² = s_n log J`, the two numeric
requirements of Lemma 4 (`log 2 ≤ M² n ε²/(16σ²)` and
`2 m log J + n ε² ≤ M² n ε²/(16σ²)`) follow from `16σ²(2A+1) ≤ M²` and `log 2 ≤ n ε²`. -/
lemma master_test_arith {n : ℕ} {J σ M ε : ℝ} {A s : ℕ} (hσ : 0 < σ)
    (hnε : (n : ℝ) * ε ^ 2 = s * Real.log J) (hlog2 : Real.log 2 ≤ n * ε ^ 2)
    (h6 : 16 * σ ^ 2 * (2 * (A : ℝ) + 1) ≤ M ^ 2) :
    Real.log 2 ≤ M ^ 2 * n * ε ^ 2 / (16 * σ ^ 2) ∧
      2 * ((A * s : ℕ) : ℝ) * Real.log J + n * ε ^ 2 ≤ M ^ 2 * n * ε ^ 2 / (16 * σ ^ 2) := by
  have hnε2 : 0 ≤ (n : ℝ) * ε ^ 2 := by positivity
  have ht6 : (2 * (A : ℝ) + 1) * (n * ε ^ 2) ≤ M ^ 2 * n * ε ^ 2 / (16 * σ ^ 2) := by
    have hσ2 : 0 < 16 * σ ^ 2 := by positivity
    rw [le_div_iff₀ hσ2]
    nlinarith only [mul_le_mul_of_nonneg_right h6 hnε2]
  refine ⟨?_, ?_⟩
  · have hA : (1 : ℝ) ≤ 2 * (A : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) A]
    have hscale : (n : ℝ) * ε ^ 2 ≤ (2 * (A : ℝ) + 1) * (n * ε ^ 2) := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hA hnε2
    exact hlog2.trans (hscale.trans ht6)
  · have : 2 * ((A * s : ℕ) : ℝ) * Real.log J + n * ε ^ 2 = (2 * (A : ℝ) + 1) * (n * ε ^ 2) := by
      rw [hnε]; push_cast; ring
    rw [this]; exact ht6

/-- **Step: the type II errors integrate to the test bound.** On `U ∩ Θᶜ` each test error is at
most `exp(−M² n ε²/(64σ²))`, so by `Π ≤ 1` the integral over that set obeys the same bound. -/
lemma master_typeII_integral {n J : ℕ} {σ : ℝ} {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ}
    {pdf : ℝ → ℝ} {δ M ε : ℝ} {m : ℕ} {R : Set (Fin n → ℝ)}
    [IsProbabilityMeasure (prior J pdf)]
    (hR1 : ∀ θ : Fin J → ℝ, numLarge δ θ ≤ m → M * ε < empNorm (X *ᵥ θ - f₀) →
      dataLaw σ (X *ᵥ θ) Rᶜ ≤ ENNReal.ofReal (Real.exp (-(M ^ 2 * n * ε ^ 2 / (64 * σ ^ 2))))) :
    ∫⁻ θ in farSet X f₀ (M * ε) ∩ (denseSet δ m)ᶜ, dataLaw σ (X *ᵥ θ) Rᶜ ∂(prior J pdf) ≤
      ENNReal.ofReal (Real.exp (-(M ^ 2 * (n * ε ^ 2) / (64 * σ ^ 2)))) := by
  calc ∫⁻ θ in farSet X f₀ (M * ε) ∩ (denseSet δ m)ᶜ, dataLaw σ (X *ᵥ θ) Rᶜ ∂(prior J pdf)
      ≤ ∫⁻ _θ in farSet X f₀ (M * ε) ∩ (denseSet δ m)ᶜ,
          ENNReal.ofReal (Real.exp (-(M ^ 2 * (n * ε ^ 2) / (64 * σ ^ 2)))) ∂(prior J pdf) := by
        apply setLIntegral_mono measurable_const
        intro θ hθ
        have h1 : M * ε < empNorm (X *ᵥ θ - f₀) := hθ.1
        have h2 : numLarge δ θ ≤ m := by
          have := hθ.2
          simp only [denseSet, Set.mem_compl_iff, Set.mem_ofPred_eq, not_lt] at this
          exact this
        have := hR1 θ h2 h1
        have e : M ^ 2 * n * ε ^ 2 = M ^ 2 * (n * ε ^ 2) := by ring
        rw [e] at this
        exact this
    _ = ENNReal.ofReal (Real.exp (-(M ^ 2 * (n * ε ^ 2) / (64 * σ ^ 2)))) *
          prior J pdf (farSet X f₀ (M * ε) ∩ (denseSet δ m)ᶜ) := setLIntegral_const _ _
    _ ≤ ENNReal.ofReal (Real.exp (-(M ^ 2 * (n * ε ^ 2) / (64 * σ ^ 2)))) * 1 := by
        gcongr; exact prob_le_one
    _ = _ := mul_one _

/-- **Step: the far-set bound.** The posterior decomposition (test set `R`, sieve `Θ`) combined
with the evidence, sieve, test and type II bounds gives `E₀ Π(U | Y) ≤ 5 e^{−n ε̃²}`. -/
lemma master_far_bound {n J : ℕ} {σ : ℝ} (hσ : 0 < σ) (X : Matrix (Fin n) (Fin J) ℝ)
    (f₀ : Fin n → ℝ) (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri]
    {U Θ : Set (Fin J → ℝ)} {R : Set (Fin n → ℝ)} (hU : MeasurableSet U)
    (hΘ : MeasurableSet Θ) (hR : MeasurableSet R) {dstar e2 et2 s t : ℝ} (hd : 0 < dstar)
    (hRb : dataLaw σ f₀ R ≤ ENNReal.ofReal (2 * Real.exp (-e2)))
    (hev : dataLaw σ f₀ {y | evidence σ X f₀ pri y < ENNReal.ofReal dstar} ≤
      ENNReal.ofReal (Real.exp (-et2)))
    (hΘb : pri Θ ≤ ENNReal.ofReal (Real.exp (-s)))
    (hint : ∫⁻ θ in U ∩ Θᶜ, dataLaw σ (X *ᵥ θ) Rᶜ ∂pri ≤ ENNReal.ofReal (Real.exp (-t)))
    (hs2 : dstar⁻¹ * Real.exp (-s) ≤ Real.exp (-e2))
    (ht2 : dstar⁻¹ * Real.exp (-t) ≤ Real.exp (-e2))
    (hmono : Real.exp (-e2) ≤ Real.exp (-et2)) :
    ∫⁻ y, posterior σ X f₀ pri y U ∂(dataLaw σ f₀) ≤ ENNReal.ofReal (5 * Real.exp (-et2)) := by
  have key := posterior_decomposition hσ X f₀ pri hU hΘ hR hd
  have hdinv : 0 ≤ dstar⁻¹ := (inv_pos.mpr hd).le
  calc ∫⁻ y, posterior σ X f₀ pri y U ∂(dataLaw σ f₀)
      ≤ ENNReal.ofReal (2 * Real.exp (-e2)) + ENNReal.ofReal (Real.exp (-et2)) +
          ENNReal.ofReal dstar⁻¹ *
            (ENNReal.ofReal (Real.exp (-s)) + ENNReal.ofReal (Real.exp (-t))) := by
        refine key.trans ?_
        gcongr
    _ = ENNReal.ofReal (2 * Real.exp (-e2) + Real.exp (-et2) +
          dstar⁻¹ * (Real.exp (-s) + Real.exp (-t))) :=
        ofReal_combine (by positivity) (by positivity) hdinv (by positivity) (by positivity)
    _ ≤ ENNReal.ofReal (5 * Real.exp (-et2)) := by
        apply ENNReal.ofReal_le_ofReal
        rw [mul_add]
        linarith [hs2, ht2, hmono]

/-- **Step: the dense-set bound.** The posterior decomposition with `R = ∅` and `U = Θ`
combined with the evidence and sieve bounds gives `E₀ Π(Θ | Y) ≤ 2 e^{−n ε̃²}`. -/
lemma master_dense_bound {n J : ℕ} {σ : ℝ} (hσ : 0 < σ) (X : Matrix (Fin n) (Fin J) ℝ)
    (f₀ : Fin n → ℝ) (pri : Measure (Fin J → ℝ)) [IsProbabilityMeasure pri]
    {Θ : Set (Fin J → ℝ)} (hΘ : MeasurableSet Θ) {dstar e2 et2 s : ℝ} (hd : 0 < dstar)
    (hev : dataLaw σ f₀ {y | evidence σ X f₀ pri y < ENNReal.ofReal dstar} ≤
      ENNReal.ofReal (Real.exp (-et2)))
    (hΘb : pri Θ ≤ ENNReal.ofReal (Real.exp (-s)))
    (hs2 : dstar⁻¹ * Real.exp (-s) ≤ Real.exp (-e2))
    (hmono : Real.exp (-e2) ≤ Real.exp (-et2)) :
    ∫⁻ y, posterior σ X f₀ pri y Θ ∂(dataLaw σ f₀) ≤ ENNReal.ofReal (2 * Real.exp (-et2)) := by
  have hdinv : 0 ≤ dstar⁻¹ := (inv_pos.mpr hd).le
  have key := posterior_decomposition (R := ∅) hσ X f₀ pri hΘ hΘ MeasurableSet.empty hd
  simp only [measure_empty, zero_add, Set.inter_compl_self, setLIntegral_empty,
    add_zero] at key
  calc ∫⁻ y, posterior σ X f₀ pri y Θ ∂(dataLaw σ f₀)
      ≤ ENNReal.ofReal (Real.exp (-et2)) +
          ENNReal.ofReal dstar⁻¹ * ENNReal.ofReal (Real.exp (-s)) := by
        refine key.trans ?_
        gcongr
    _ = ENNReal.ofReal (Real.exp (-et2) + dstar⁻¹ * Real.exp (-s)) := by
        rw [← ENNReal.ofReal_mul hdinv, ← ENNReal.ofReal_add (by positivity) (by positivity)]
    _ ≤ ENNReal.ofReal (2 * Real.exp (-et2)) := by
        apply ENNReal.ofReal_le_ofReal
        linarith [hs2, hmono]

/-- **Theorem 1, non-asymptotic form.** -/
theorem master_theorem : MasterStatement := by
  intro n J σ X f₀ pdf εt δ E M a K η μ c4 c5 h
  obtain ⟨θ₀, S, hA2, h4⟩ := h.approx
  have : IsProbabilityMeasure (prior J pdf) := isProbabilityMeasure_prior h.hpdf J
  have hn := h.hn
  have hJ := h.hJ
  have hσ := h.hσ
  -- rates and constants
  have hs1 : 1 ≤ sRate n J a εt := one_le_sRate h.ha1
  have hnε : (n : ℝ) * epsRate n J a εt ^ 2 = sRate n J a εt * Real.log J :=
    mul_epsRate_sq hn hJ a εt
  have hεtε : εt ≤ epsRate n J a εt := epsRate_ge hn hJ a h.hεt.le
  have hlog2 : Real.log 2 ≤ n * epsRate n J a εt ^ 2 := log_two_le_mul_epsRate_sq hn hJ h.ha1 εt
  have hC0 : 0 ≤ C1 K η σ c4 c5 := C1_nonneg h.hK.le h.hη.le hσ h.hc4 h.hc5
  have hA1 : 1 ≤ Aconst K η σ μ c4 c5 := one_le_Aconst h.hμ hC0
  have hμA : C1 K η σ c4 c5 + 1 ≤ μ * Aconst K η σ μ c4 c5 := le_mu_mul_Aconst h.hμ
  have hMpos : 0 < M := by have := h.e5; have := h.hK; linarith
  have hm : 1 ≤ Aconst K η σ μ c4 c5 * sRate n J a εt := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (Nat.one_le_iff_ne_zero.mp hA1) (Nat.one_le_iff_ne_zero.mp hs1))
  have hnε2 : 0 ≤ (n : ℝ) * epsRate n J a εt ^ 2 := by positivity
  have hnεt : (n : ℝ) * εt ^ 2 ≤ n * epsRate n J a εt ^ 2 := by
    have : εt ^ 2 ≤ epsRate n J a εt ^ 2 := pow_le_pow_left₀ h.hεt.le hεtε 2
    exact mul_le_mul_of_nonneg_left this (Nat.cast_nonneg n)
  -- Lemma 1 and Lemma 2: evidence
  have hmass := local_mass h.hJ h.hpdf h.hεt h.hδ h.hE h.ha1 h.haJ h.hK h.hη h.hμ h.hc4 h.hc5
    h.hδεt h.basis hA2 h4 h.wg3 h.wg5 h.e1 h.e2 h.e3
  have hev := evidence_lower hσ hn X f₀ (prior J pdf) (Ltil_pos h.hK.le h.hη.le) h.hεt
    (CPi_pos h.hc4 h.hc5).le hmass
  rw [← C1_eq] at hev
  -- Lemma 3: sieve
  have hsieve := sieve_mass_exp h.hpdf (by omega) h.hμ h.wg3
    (Aconst K η σ μ c4 c5 * sRate n J a εt)
  have hsieve_exp : μ * ((Aconst K η σ μ c4 c5 * sRate n J a εt : ℕ) : ℝ) * Real.log J =
      μ * Aconst K η σ μ c4 c5 * (n * epsRate n J a εt ^ 2) := by
    rw [hnε]; push_cast; ring
  rw [hsieve_exp] at hsieve
  -- Lemma 4: tests
  obtain ⟨ht, hmt⟩ := master_test_arith (A := Aconst K η σ μ c4 c5) (s := sRate n J a εt)
    hσ hnε hlog2 h.e6
  obtain ⟨R, hRm, hR0, hR1⟩ := tests_exist hσ hn hJ (Aconst K η σ μ c4 c5 * sRate n J a εt)
    h.hK.le h.basis h.hδ.le h.hδεt h.hεt hεtε hMpos h.e5 h.e4 hm ht hmt
  -- abbreviations for the final bookkeeping
  set dstar : ℝ := Real.exp (-(C1 K η σ c4 c5 * (n * εt ^ 2))) with hdstar
  have hdpos : 0 < dstar := Real.exp_pos _
  have hev' : dataLaw σ f₀ {y | evidence σ X f₀ (prior J pdf) y < ENNReal.ofReal dstar} ≤
      ENNReal.ofReal (Real.exp (-(n * εt ^ 2))) := by
    have : -(C1 K η σ c4 c5 * n * εt ^ 2) = -(C1 K η σ c4 c5 * (n * εt ^ 2)) := by ring
    rw [this] at hev; exact hev
  have hU := measurableSet_farSet X f₀ (M * epsRate n J a εt)
  have hΘ := measurableSet_denseSet (J := J) δ (Aconst K η σ μ c4 c5 * sRate n J a εt)
  -- the integral of the type II errors
  have hint := master_typeII_integral (σ := σ) (X := X) (f₀ := f₀) (pdf := pdf) (δ := δ) (M := M)
    (ε := epsRate n J a εt) (m := Aconst K η σ μ c4 c5 * sRate n J a εt) (R := R) hR1
  -- real inequalities
  have hsr := master_sieve_real (μA := μ * Aconst K η σ μ c4 c5) hC0 hnεt hμA hnε2
  have htr := master_test_real hC0 hσ hnεt hnε2 h.e7
  rw [← hdstar] at hsr htr
  have hεmono : Real.exp (-(n * epsRate n J a εt ^ 2)) ≤ Real.exp (-(n * εt ^ 2)) :=
    Real.exp_le_exp.mpr (by linarith)
  constructor
  · -- E₀ Π(U | Y) ≤ 5 e^{−n ε̃²}
    exact master_far_bound hσ X f₀ (prior J pdf) hU hΘ hRm hdpos hR0 hev' hsieve hint hsr htr
      hεmono
  · -- E₀ Π(Θ | Y) ≤ 2 e^{−n ε̃²}
    exact master_dense_bound hσ X f₀ (prior J pdf) hΘ hdpos hev' hsieve hsr hεmono

end LargePrior
