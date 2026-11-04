import LargePrior.VdPBasics
import LargePrior.Fejer

/-!
# The de la Vallée Poussin smoother: stability and the univariate error bound (blueprint §F.2–F.3)
-/

open MeasureTheory Finset intervalIntegral
open scoped Real

noncomputable section

namespace LargePrior

/-- `Q_m` for `m ≤ 2` is the mean `⟨g, ψ₀⟩`. -/
private lemma Qop_small {m : ℕ} (hm : m ≤ 2) (g : ℝ → ℝ) (x : ℝ) : Qop m g x = coef g 0 := by
  simp [Qop, budgetAtoms, hm, qMult, freq, fourierAtom]

/-- `Q_m g(x) = ∫₀¹ g(t) K_m(x,t) dt` with the kernel written as a finite sum of atoms. -/
private lemma Qop_eq_integral (m : ℕ) {g : ℝ → ℝ} (hg : Continuous g) (x : ℝ) :
    Qop m g x = ∫ t in (0 : ℝ)..1, g t * ∑ ν ∈ range (budgetAtoms m),
      qMult m (freq ν) * fourierAtom ν x * fourierAtom ν t := by
  have hint : ∀ ν ∈ range (budgetAtoms m), IntervalIntegrable
      (fun t => g t * (qMult m (freq ν) * fourierAtom ν x * fourierAtom ν t)) volume 0 1 := by
    intro ν _
    exact (hg.mul (continuous_const.mul (continuous_fourierAtom ν))).intervalIntegrable 0 1
  simp_rw [Finset.mul_sum]
  rw [intervalIntegral.integral_finsetSum hint]
  unfold Qop coef
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [show qMult m (freq ν) * (∫ t in (0 : ℝ)..1, g t * fourierAtom ν t) * fourierAtom ν x =
      (qMult m (freq ν) * fourierAtom ν x) * ∫ t in (0 : ℝ)..1, g t * fourierAtom ν t by ring,
    ← intervalIntegral.integral_const_mul]
  congr 1
  funext t
  ring

/-- The second Fejér sum, extended to the range `1..2q−1` with positive parts. -/
private lemma fejer_sum_extend {q : ℕ} (hq : 1 ≤ q) (u : ℝ) :
    ∑ j ∈ Icc 1 (q - 1), (1 - (j : ℝ) / (((q - 1 : ℕ) : ℝ) + 1)) * Real.cos (2 * π * j * u) =
      ∑ j ∈ Icc 1 (2 * q - 1), max 0 (1 - (j : ℝ) / q) * Real.cos (2 * π * j * u) := by
  have hcast : ((q - 1 : ℕ) : ℝ) + 1 = q := by
    rw [Nat.cast_sub hq]; simp
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  rw [hcast]
  apply Finset.sum_subset_zero_on_sdiff
  · intro j hj
    simp only [mem_Icc] at hj ⊢
    omega
  · intro j hj
    simp only [mem_sdiff, mem_Icc] at hj
    have hjq : (q : ℝ) ≤ j := by exact_mod_cast (by omega : q ≤ j)
    have : 1 - (j : ℝ) / q ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hqpos]; linarith
    rw [max_eq_left this, zero_mul]
  · intro j hj
    simp only [mem_Icc] at hj
    have hjq : (j : ℝ) < q := by exact_mod_cast (by omega : j < q)
    have : 0 ≤ 1 - (j : ℝ) / q := by
      rw [sub_nonneg, div_le_one hqpos]; exact hjq.le
    rw [max_eq_right this]

/-- The first Fejér sum: on `1..2q−1` the positive part is inactive. -/
private lemma fejer_sum_first {q : ℕ} (hq : 1 ≤ q) (u : ℝ) :
    ∑ j ∈ Icc 1 (2 * q - 1), (1 - (j : ℝ) / (((2 * q - 1 : ℕ) : ℝ) + 1)) *
        Real.cos (2 * π * j * u) =
      ∑ j ∈ Icc 1 (2 * q - 1), max 0 (1 - (j : ℝ) / (2 * q)) * Real.cos (2 * π * j * u) := by
  have hcast : ((2 * q - 1 : ℕ) : ℝ) + 1 = 2 * q := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hqpos : (0 : ℝ) < 2 * q := by positivity
  rw [hcast]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [mem_Icc] at hj
  have hjq : (j : ℝ) ≤ 2 * q := by exact_mod_cast (by omega : j ≤ 2 * q)
  have : 0 ≤ 1 - (j : ℝ) / (2 * q) := by
    rw [sub_nonneg, div_le_one hqpos]; exact hjq
  rw [max_eq_right this]

/-- Kernel identity: for `m ≥ 3`, `K_m(x,t) = 2 F_{2q−1}(x−t) − F_{q−1}(x−t)`, `q = q_m`. -/
private lemma kernel_eq {m : ℕ} (hm : 3 ≤ m) (x t : ℝ) :
    ∑ ν ∈ range (budgetAtoms m), qMult m (freq ν) * fourierAtom ν x * fourierAtom ν t =
      2 * fejerKernel (2 * budgetDeg m - 1) (x - t) - fejerKernel (budgetDeg m - 1) (x - t) := by
  set q := budgetDeg m with hqdef
  have hq : 1 ≤ q := (budgetDeg_bounds hm).1
  have hA : budgetAtoms m = 2 * (2 * q - 1) + 1 := by
    simp only [budgetAtoms, show ¬ m ≤ 2 by omega, ↓reduceIte]; omega
  have hQ : ∀ j, qMult m j = vdpMult q j := fun j => by
    simp [qMult, show ¬ m ≤ 2 by omega, hqdef]
  rw [hA, sum_range_pair]
  have h0 : qMult m (freq 0) * fourierAtom 0 x * fourierAtom 0 t = 1 := by
    simp [hQ, vdpMult, freq, fourierAtom]; norm_num
  have hpair : ∀ j ∈ Icc 1 (2 * q - 1),
      qMult m (freq (2 * j - 1)) * fourierAtom (2 * j - 1) x * fourierAtom (2 * j - 1) t +
        qMult m (freq (2 * j)) * fourierAtom (2 * j) x * fourierAtom (2 * j) t =
      2 * (2 * max 0 (1 - (j : ℝ) / (2 * q)) * Real.cos (2 * π * j * (x - t))) -
        2 * (max 0 (1 - (j : ℝ) / q) * Real.cos (2 * π * j * (x - t))) := by
    intro j hj
    have hj1 : 1 ≤ j := (mem_Icc.1 hj).1
    obtain ⟨f1, f2⟩ := freq_spec hj1
    have hp := fourierAtom_pair hj1 x t
    rw [f1, f2, hQ]
    simp only [vdpMult] at *
    linear_combination (2 * max 0 (1 - (j : ℝ) / (2 * q)) - max 0 (1 - (j : ℝ) / q)) * hp
  rw [h0, Finset.sum_congr rfl hpair, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  unfold fejerKernel
  rw [fejer_sum_first hq, fejer_sum_extend hq]
  have : ∑ j ∈ Icc 1 (2 * q - 1), 2 * max 0 (1 - (j : ℝ) / (2 * q)) *
      Real.cos (2 * π * j * (x - t)) =
      2 * ∑ j ∈ Icc 1 (2 * q - 1), max 0 (1 - (j : ℝ) / (2 * q)) *
      Real.cos (2 * π * j * (x - t)) := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun j _ => by ring
  rw [this]
  ring

/-- Stability (eq:vdp-stable): `|Q_m g| ≤ 3A` when `g` is continuous and `|g| ≤ A`. -/
lemma Qop_stable {g : ℝ → ℝ} {A : ℝ} (hg : Continuous g) (hA : ∀ t, |g t| ≤ A) (m : ℕ)
    (x : ℝ) : |Qop m g x| ≤ 3 * A := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  rcases le_or_gt m 2 with hm | hm
  · rw [Qop_small hm]
    linarith [coef_abs_le hg hA 0]
  · have hm3 : 3 ≤ m := hm
    set N₁ := 2 * budgetDeg m - 1
    set N₂ := budgetDeg m - 1
    rw [Qop_eq_integral m hg x]
    simp_rw [kernel_eq hm3 x]
    have hc₁ := continuous_fejerKernel N₁
    have hc₂ := continuous_fejerKernel N₂
    have hbound : IntervalIntegrable
        (fun t => A * (2 * fejerKernel N₁ (x - t) + fejerKernel N₂ (x - t))) volume 0 1 :=
      (continuous_const.mul ((continuous_const.mul (hc₁.comp (continuous_const.sub
        continuous_id))).add (hc₂.comp (continuous_const.sub continuous_id)))).intervalIntegrable
        0 1
    have key := intervalIntegral.norm_integral_le_of_norm_le (μ := volume)
      (f := fun t => g t * (2 * fejerKernel N₁ (x - t) - fejerKernel N₂ (x - t)))
      zero_le_one (Filter.Eventually.of_forall fun t _ => by
        have h1 := fejerKernel_nonneg N₁ (x - t)
        have h2 := fejerKernel_nonneg N₂ (x - t)
        rw [Real.norm_eq_abs, abs_mul]
        have hK : |2 * fejerKernel N₁ (x - t) - fejerKernel N₂ (x - t)| ≤
            2 * fejerKernel N₁ (x - t) + fejerKernel N₂ (x - t) := by
          rw [abs_le]; constructor <;> linarith
        exact mul_le_mul (hA t) hK (abs_nonneg _) hA0) hbound
    have hval : ∫ t in (0 : ℝ)..1, A * (2 * fejerKernel N₁ (x - t) + fejerKernel N₂ (x - t)) =
        3 * A := by
      rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add
        (f := fun t => 2 * fejerKernel N₁ (x - t)) (g := fun t => fejerKernel N₂ (x - t))
        ((continuous_const.mul (hc₁.comp (continuous_const.sub continuous_id))).intervalIntegrable
          0 1) ((hc₂.comp (continuous_const.sub continuous_id)).intervalIntegrable 0 1),
        intervalIntegral.integral_const_mul, integral_fejerKernel_sub, integral_fejerKernel_sub]
      ring
    rw [Real.norm_eq_abs, hval] at key
    exact key

/-- **Univariate error bound** (eq:coordinate-Jackson): given the Jackson inequality, every `g`
in the Hölder–Zygmund ball of radius `R` has `|g − Q_m g| ≤ C'_α R m^{−α}` for every `m ≥ 1`. -/
lemma Qop_error {α : ℝ} {r : ℕ} {C R : ℝ} {g : ℝ → ℝ} (hα : 0 < α) (hJ : JacksonIneq α r C)
    (hg : HZBall1 α r R g) {m : ℕ} (hm : 1 ≤ m) (x : ℝ) :
    |g x - Qop m g x| ≤ jackC' α C * R * (m : ℝ) ^ (-α) := by
  have hg' := hg
  obtain ⟨hgc, -, A, B, hA0, hB0, hAB, hAbd, -⟩ := hg'
  have hR : 0 ≤ R := by linarith
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmα : 0 ≤ (m : ℝ) ^ (-α) := Real.rpow_nonneg hmpos.le _
  rcases le_or_gt m 2 with hm2 | hm2
  · rw [Qop_small hm2]
    have h1 : |g x - coef g 0| ≤ 2 * R := by
      have := coef_abs_le hgc hAbd 0
      have := hAbd x
      calc |g x - coef g 0| ≤ |g x| + |coef g 0| := abs_sub _ _
        _ ≤ 2 * R := by linarith
    have hm2' : (m : ℝ) ≤ 2 := by exact_mod_cast hm2
    have h2 : (2 : ℝ) ^ (-α) ≤ (m : ℝ) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hmpos hm2' (by linarith)
    have h3 : (2 : ℝ) ^ (1 + α) * (2 : ℝ) ^ (-α) = 2 := by
      rw [← Real.rpow_add (by norm_num)]; norm_num
    have h4 : (2 : ℝ) ^ (1 + α) ≤ jackC' α C := le_max_right _ _
    have h5 : 0 ≤ (2 : ℝ) ^ (1 + α) := Real.rpow_nonneg (by norm_num) _
    calc |g x - coef g 0| ≤ 2 * R := h1
      _ = (2 : ℝ) ^ (1 + α) * R * (2 : ℝ) ^ (-α) := by rw [mul_right_comm, h3]
      _ ≤ jackC' α C * R * (m : ℝ) ^ (-α) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_right h4 hR) h2
          (Real.rpow_nonneg (by norm_num) _) ((mul_nonneg h5 hR).trans
            (mul_le_mul_of_nonneg_right h4 hR))
  · have hm3 : 3 ≤ m := hm2
    obtain ⟨hq1, hq8⟩ := budgetDeg_bounds hm3
    obtain ⟨p, hpoly, hp⟩ := hJ R g hg (budgetDeg m) hq1
    have hpcont : Continuous p := by
      obtain ⟨c, hpc⟩ := hpoly
      rw [show p = fun y => ∑ ν ∈ range (2 * budgetDeg m + 1), c ν * fourierAtom ν y from
        funext hpc]
      exact continuous_finsetSum _ fun ν _ => continuous_const.mul (continuous_fourierAtom ν)
    have hqpos : (0 : ℝ) < budgetDeg m := by exact_mod_cast hq1
    have hE : ∀ t, |(g - p) t| ≤ C * R * (budgetDeg m : ℝ) ^ (-α) := fun t => by
      simpa using hp t
    have hstab := Qop_stable (hgc.sub hpcont) hE m x
    have hdecomp : g x - Qop m g x = (g x - p x) - Qop m (g - p) x := by
      rw [Qop_sub hgc hpcont m x, Qop_trigPoly hm3 le_rfl hpoly x]; ring
    have h1 : |g x - Qop m g x| ≤ 4 * (C * R * (budgetDeg m : ℝ) ^ (-α)) := by
      rw [hdecomp]
      calc |(g x - p x) - Qop m (g - p) x| ≤ |g x - p x| + |Qop m (g - p) x| := abs_sub _ _
        _ ≤ 4 * (C * R * (budgetDeg m : ℝ) ^ (-α)) := by linarith [hp x]
    have hCR : 0 ≤ C * R :=
      nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hp x)) (Real.rpow_pos_of_pos hqpos _)
    have hm8 : (0 : ℝ) < (m : ℝ) / 8 := by positivity
    have h2 : (budgetDeg m : ℝ) ^ (-α) ≤ 8 ^ α * (m : ℝ) ^ (-α) := by
      calc (budgetDeg m : ℝ) ^ (-α) ≤ ((m : ℝ) / 8) ^ (-α) :=
            Real.rpow_le_rpow_of_nonpos hm8 hq8 (by linarith)
        _ = 8 ^ α * (m : ℝ) ^ (-α) := by
            rw [Real.div_rpow hmpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 8),
              div_inv_eq_mul, mul_comm]
    have h4 : 4 * 8 ^ α * C ≤ jackC' α C := le_max_left _ _
    calc |g x - Qop m g x| ≤ 4 * (C * R * (budgetDeg m : ℝ) ^ (-α)) := h1
      _ ≤ 4 * (C * R * (8 ^ α * (m : ℝ) ^ (-α))) := by gcongr
      _ = (4 * 8 ^ α * C) * (R * (m : ℝ) ^ (-α)) := by ring
      _ ≤ jackC' α C * (R * (m : ℝ) ^ (-α)) :=
            mul_le_mul_of_nonneg_right h4 (mul_nonneg hR hmα)
      _ = jackC' α C * R * (m : ℝ) ^ (-α) := by ring

end LargePrior
