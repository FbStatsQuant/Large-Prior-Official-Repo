import LargePrior.Covering
import LargePrior.BasicTest

/-!
# Lemma 4: tests (`lem:tests`)
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

variable {n J : ℕ}

/-- Type I error of one basic test whose centre lies in shell `k + 1`:
`P₀(R_g) ≤ exp(−(k+1) t)` with `t = M² n ε² / (16σ²)`. -/
private lemma typeI_one {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n) {f₀ g : Fin n → ℝ} {M ε : ℝ}
    (hMε : 0 < M * ε) (k : ℕ) (hg : 15 / 16 * ((k : ℝ) + 1) * M * ε ≤ empNorm (g - f₀)) :
    dataLaw σ f₀ (testRegion f₀ g) ≤
      ENNReal.ofReal (Real.exp (-(((k : ℝ) + 1) * (M ^ 2 * n * ε ^ 2 / (16 * σ ^ 2))))) := by
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  have hd : 0 < empNorm (g - f₀) := lt_of_lt_of_le (by
    have : 15 / 16 * ((k : ℝ) + 1) * M * ε = 15 / 16 * ((k : ℝ) + 1) * (M * ε) := by ring
    rw [this]; positivity) hg
  refine (basic_test_typeI hσ hn hd).trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  rw [neg_le_neg_iff]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hd2 : (15 / 16 * ((k : ℝ) + 1) * (M * ε)) ^ 2 ≤ empNorm (g - f₀) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity); linarith
  have hkk : ((k : ℝ) + 1) * (M * ε) ^ 2 ≤ ((k : ℝ) + 1) ^ 2 * (M * ε) ^ 2 := by
    apply mul_le_mul_of_nonneg_right _ (by positivity); nlinarith
  have key : ((k : ℝ) + 1) * (M ^ 2 * ε ^ 2) * 8 ≤ empNorm (g - f₀) ^ 2 * 16 := by
    nlinarith
  have key' := mul_le_mul_of_nonneg_right key (le_of_lt (mul_pos hnr hσ2))
  rw [← mul_div_assoc, div_le_div_iff₀ (by positivity) (by positivity)]
  linarith

/-- Real bound for one shell: `#G_k · exp(−(k+1) t) ≤ exp(−n ε²) · 2⁻ᵏ`. -/
private lemma shell_real_bound {L t c C : ℝ} (ht : Real.log 2 ≤ t) (hLt : L + c ≤ t)
    (hC : C ≤ Real.exp L) (k : ℕ) :
    C * Real.exp (-(((k : ℝ) + 1) * t)) ≤ Real.exp (-c) * (2⁻¹ : ℝ) ^ k := by
  have he : Real.exp (-t) ≤ 2⁻¹ := by
    calc Real.exp (-t) ≤ Real.exp (-Real.log 2) := Real.exp_le_exp.2 (by linarith)
      _ = 2⁻¹ := by rw [Real.exp_neg, Real.exp_log (by norm_num)]
  have hsplit : Real.exp (-(((k : ℝ) + 1) * t)) = Real.exp (-t) * Real.exp (-t) ^ k := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; congr 1; ring
  rw [hsplit]
  calc C * (Real.exp (-t) * Real.exp (-t) ^ k)
      ≤ Real.exp L * (Real.exp (-t) * Real.exp (-t) ^ k) :=
        mul_le_mul_of_nonneg_right hC (by positivity)
    _ = Real.exp (L - t) * Real.exp (-t) ^ k := by
        rw [sub_eq_add_neg, Real.exp_add]; ring
    _ ≤ Real.exp (-c) * (2⁻¹ : ℝ) ^ k := by
        apply mul_le_mul (Real.exp_le_exp.2 (by linarith))
          (pow_le_pow_left₀ (by positivity) he k) (by positivity) (by positivity)

/-- Type I error of the union test. -/
private lemma typeI_union {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n) {f₀ : Fin n → ℝ} {M ε L : ℝ}
    (hMε : 0 < M * ε) (G : ℕ → Finset (Fin n → ℝ))
    (hcard : ∀ k, ((G k).card : ℝ) ≤ Real.exp L)
    (hdist : ∀ k : ℕ, ∀ g ∈ G k, 15 / 16 * ((k : ℝ) + 1) * M * ε ≤ empNorm (g - f₀))
    (ht : Real.log 2 ≤ M ^ 2 * n * ε ^ 2 / (16 * σ ^ 2))
    (hLt : L + n * ε ^ 2 ≤ M ^ 2 * n * ε ^ 2 / (16 * σ ^ 2)) :
    dataLaw σ f₀ (⋃ k, ⋃ g ∈ G k, testRegion f₀ g) ≤
      ENNReal.ofReal (2 * Real.exp (-(n * ε ^ 2))) := by
  set t := M ^ 2 * n * ε ^ 2 / (16 * σ ^ 2) with htdef
  have hterm : ∀ k, ∑ g ∈ G k, dataLaw σ f₀ (testRegion f₀ g) ≤
      ENNReal.ofReal (Real.exp (-(n * ε ^ 2))) * 2⁻¹ ^ k := by
    intro k
    calc ∑ g ∈ G k, dataLaw σ f₀ (testRegion f₀ g)
        ≤ ∑ _g ∈ G k, ENNReal.ofReal (Real.exp (-(((k : ℝ) + 1) * t))) :=
          Finset.sum_le_sum fun g hg => typeI_one hσ hn hMε k (hdist k g hg)
      _ = ENNReal.ofReal ((G k).card * Real.exp (-(((k : ℝ) + 1) * t))) := by
          rw [Finset.sum_const, nsmul_eq_mul, ENNReal.ofReal_mul (by positivity),
            ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (Real.exp (-(n * ε ^ 2)) * (2⁻¹ : ℝ) ^ k) :=
          ENNReal.ofReal_le_ofReal (shell_real_bound ht hLt (hcard k) k)
      _ = ENNReal.ofReal (Real.exp (-(n * ε ^ 2))) * 2⁻¹ ^ k := by
          rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by norm_num),
            ENNReal.ofReal_inv_of_pos (by norm_num), ENNReal.ofReal_ofNat]
  calc dataLaw σ f₀ (⋃ k, ⋃ g ∈ G k, testRegion f₀ g)
      ≤ ∑' k, dataLaw σ f₀ (⋃ g ∈ G k, testRegion f₀ g) := measure_iUnion_le _
    _ ≤ ∑' k, ∑ g ∈ G k, dataLaw σ f₀ (testRegion f₀ g) :=
        ENNReal.tsum_le_tsum fun k => measure_biUnion_finset_le _ _
    _ ≤ ∑' k : ℕ, ENNReal.ofReal (Real.exp (-(n * ε ^ 2))) * 2⁻¹ ^ k :=
        ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (2 * Real.exp (-(n * ε ^ 2))) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv,
          ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_ofNat, mul_comm]

/-- Shell selection: if `a < E` (with `a > 0`) then `(k+1) a < E ≤ (k+2) a` for some `k`. -/
private lemma exists_shell {a E : ℝ} (ha : 0 < a) (hE : a < E) :
    ∃ k : ℕ, ((k : ℝ) + 1) * a < E ∧ E ≤ ((k : ℝ) + 1 + 1) * a := by
  set x := E / a with hxdef
  have hx : 1 < x := by rw [hxdef, lt_div_iff₀ ha]; linarith
  have h1 : 1 < ⌈x⌉₊ := Nat.lt_ceil.2 (by exact_mod_cast hx)
  obtain ⟨k, hk⟩ : ∃ k, ⌈x⌉₊ = k + 2 := ⟨⌈x⌉₊ - 2, by omega⟩
  have hup : x ≤ (k : ℝ) + 2 := by
    have := Nat.le_ceil x; rw [hk] at this; push_cast at this; exact this
  have hlo : (k : ℝ) + 2 < x + 1 := by
    have := Nat.ceil_lt_add_one (by linarith : 0 ≤ x); rw [hk] at this; push_cast at this
    exact this
  refine ⟨k, ?_, ?_⟩
  · rw [← lt_div_iff₀ ha]; linarith
  · rw [← div_le_iff₀ ha]; linarith

/-- Type II error of the union test. -/
private lemma typeII_union {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n) {X : Matrix (Fin n) (Fin J) ℝ}
    {f₀ : Fin n → ℝ} {δ M ε : ℝ} {m : ℕ} (hMε : 0 < M * ε) (G : ℕ → Finset (Fin n → ℝ))
    (hdist : ∀ k : ℕ, ∀ g ∈ G k, 15 / 16 * ((k : ℝ) + 1) * M * ε ≤ empNorm (g - f₀))
    (hcov : ∀ k : ℕ, ∀ θ : Fin J → ℝ, numLarge δ θ ≤ m →
      ((k : ℝ) + 1) * M * ε < empNorm (X *ᵥ θ - f₀) →
      empNorm (X *ᵥ θ - f₀) ≤ ((k : ℝ) + 1 + 1) * M * ε →
      ∃ g ∈ G k, empNorm (X *ᵥ θ - g) ≤ ((k : ℝ) + 1) * M * ε / 8)
    (θ : Fin J → ℝ) (hθ : numLarge δ θ ≤ m) (hfar : M * ε < empNorm (X *ᵥ θ - f₀)) :
    dataLaw σ (X *ᵥ θ) (⋃ k, ⋃ g ∈ G k, testRegion f₀ g)ᶜ ≤
      ENNReal.ofReal (Real.exp (-(M ^ 2 * n * ε ^ 2 / (64 * σ ^ 2)))) := by
  obtain ⟨k, hk1, hk2⟩ := exists_shell hMε hfar
  have hk : (0 : ℝ) ≤ k := k.cast_nonneg
  obtain ⟨g, hg, hgθ⟩ := hcov k θ hθ (by rw [mul_assoc]; exact hk1) (by rw [mul_assoc]; exact hk2)
  have hdg := hdist k g hg
  have hdg' : 15 / 16 * ((k : ℝ) + 1) * (M * ε) ≤ empNorm (g - f₀) := by linarith
  have hd : 0 < empNorm (g - f₀) := lt_of_lt_of_le (by positivity) hdg'
  have hv : empNorm (X *ᵥ θ - g) ≤ empNorm (g - f₀) / 4 := by
    have : ((k : ℝ) + 1) * M * ε / 8 = ((k : ℝ) + 1) * (M * ε) / 8 := by ring
    rw [this] at hgθ
    have : 0 ≤ ((k : ℝ) + 1) * (M * ε) := by positivity
    linarith
  have hsub : (⋃ k, ⋃ g ∈ G k, testRegion f₀ g)ᶜ ⊆ (testRegion f₀ g)ᶜ :=
    Set.compl_subset_compl.2 (Set.subset_iUnion_of_subset k (Set.subset_biUnion_of_mem hg))
  refine (measure_mono hsub).trans ((basic_test_typeII hσ hn hd hv).trans
    (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)))
  rw [neg_le_neg_iff]
  have hnr : (0 : ℝ) < n := by exact_mod_cast hn
  have hσ2 : 0 < σ ^ 2 := by positivity
  have hd1 : 15 / 16 * (M * ε) ≤ empNorm (g - f₀) := by
    have : 15 / 16 * (M * ε) ≤ 15 / 16 * ((k : ℝ) + 1) * (M * ε) := by nlinarith
    linarith
  have hd2 : (15 / 16 * (M * ε)) ^ 2 ≤ empNorm (g - f₀) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hd1 2
  have key : M ^ 2 * ε ^ 2 ≤ 2 * empNorm (g - f₀) ^ 2 := by nlinarith
  have key' := mul_le_mul_of_nonneg_right key (le_of_lt (mul_pos hnr hσ2))
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **Lemma 4** (generic form): with `t = M² n ε² / (16σ²) ≥ log 2` and
`2 m log J + n ε² ≤ t`, there is a measurable rejection region `R` with `P₀(R) ≤ 2 exp(−n ε²)` and
`P_{Xθ}(Rᶜ) ≤ exp(−M² n ε² / (64σ²))` for every `θ` with `N_δ(θ) ≤ m` and
`‖Xθ − f₀‖_{2,n} > M ε`. -/
theorem tests_exist {σ : ℝ} (hσ : 0 < σ) (hn : 0 < n) (hJ : 2 ≤ J)
    {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ} {K δ εt ε M : ℝ} (m : ℕ) (hK : 0 ≤ K)
    (hX : BasisBound X K) (hδ : 0 ≤ δ) (hδεt : δ ≤ εt / J) (hεt : 0 < εt) (hεtε : εt ≤ ε)
    (hM : 0 < M) (hMK : 16 * K ≤ M) (hJ97 : 1 + Real.log 97 ≤ Real.log J) (hm : 1 ≤ m)
    (ht : Real.log 2 ≤ M ^ 2 * n * ε ^ 2 / (16 * σ ^ 2))
    (hmt : 2 * m * Real.log J + n * ε ^ 2 ≤ M ^ 2 * n * ε ^ 2 / (16 * σ ^ 2)) :
    ∃ R : Set (Fin n → ℝ), MeasurableSet R ∧
      dataLaw σ f₀ R ≤ ENNReal.ofReal (2 * Real.exp (-(n * ε ^ 2))) ∧
      ∀ θ : Fin J → ℝ, numLarge δ θ ≤ m → M * ε < empNorm (X *ᵥ θ - f₀) →
        dataLaw σ (X *ᵥ θ) Rᶜ ≤ ENNReal.ofReal (Real.exp (-(M ^ 2 * n * ε ^ 2 / (64 * σ ^ 2)))) := by
  have hMε : 0 < M * ε := mul_pos hM (lt_of_lt_of_le hεt hεtε)
  have hcov := fun k : ℕ =>
    covering (X := X) (f₀ := f₀) hn hJ m hK hX hδ hδεt hεt hεtε hM hMK hJ97 hm (k + 1) (by omega)
  choose G hGcard hGdist hGcov using hcov
  have hdist : ∀ k : ℕ, ∀ g ∈ G k, 15 / 16 * ((k : ℝ) + 1) * M * ε ≤ empNorm (g - f₀) := by
    intro k g hg; have := hGdist k g hg; push_cast at this; exact this
  have hcov' : ∀ k : ℕ, ∀ θ : Fin J → ℝ, numLarge δ θ ≤ m →
      ((k : ℝ) + 1) * M * ε < empNorm (X *ᵥ θ - f₀) →
      empNorm (X *ᵥ θ - f₀) ≤ ((k : ℝ) + 1 + 1) * M * ε →
      ∃ g ∈ G k, empNorm (X *ᵥ θ - g) ≤ ((k : ℝ) + 1) * M * ε / 8 := by
    intro k θ hθ h1 h2
    have := hGcov k θ hθ (by push_cast; exact h1) (by push_cast; exact h2)
    push_cast at this; exact this
  refine ⟨⋃ k, ⋃ g ∈ G k, testRegion f₀ g, ?_, ?_, ?_⟩
  · exact MeasurableSet.iUnion fun k =>
      Finset.measurableSet_biUnion _ fun g _ => measurableSet_testRegion f₀ g
  · exact typeI_union hσ hn hMε G hGcard hdist ht hmt
  · exact fun θ hθ hfar => typeII_union hσ hn hMε G hdist hcov' θ hθ hfar

end LargePrior
