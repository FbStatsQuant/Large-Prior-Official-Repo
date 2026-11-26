import LargePrior.CorNonVacuityS

/-!
# Optional: the Jackson inequality for `0 < α < 1`, `r = 1`

A non-vacuity witness for the classical input `JacksonIneq`: Fejér means
approximate a 1-periodic `α`-Hölder function to `O(q^{−α})` when `α < 1`. With it, the Fourier
end-to-end corollary applies to `f₀ = ψ₁` (order `1/2`, difference order `1`) with no assumed input.
The Jackson inequality and the resulting Fourier instance are both proved below.
-/

open MeasureTheory Finset

noncomputable section

namespace LargePrior

/-- `F_N ≤ N + 1`. -/
lemma fejerKernel_le_succ (N : ℕ) (s : ℝ) : fejerKernel N s ≤ N + 1 := by
  have h := fejerKernel_sumsq N s
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hc := sq_sum_le_card_mul_sum_sq (s := range (N + 1))
    (f := fun v : ℕ => Real.cos (2 * Real.pi * v * s))
  have hs := sq_sum_le_card_mul_sum_sq (s := range (N + 1))
    (f := fun v : ℕ => Real.sin (2 * Real.pi * v * s))
  have hsum : ∑ v ∈ range (N + 1),
      (Real.cos (2 * Real.pi * v * s) ^ 2 + Real.sin (2 * Real.pi * v * s) ^ 2) = N + 1 := by
    simp [Real.cos_sq_add_sin_sq]
  rw [card_range] at hc hs
  push_cast at hc hs
  rw [sum_add_distrib] at hsum
  have : ((N : ℝ) + 1) * fejerKernel N s ≤ ((N : ℝ) + 1) * (N + 1) := by
    rw [h]; nlinarith
  exact le_of_mul_le_mul_left this hN

/-- Dirichlet sums, specialized from Mathlib's division-free trigonometric identities. -/
private lemma dirichlet_pair (N : ℕ) (x : ℝ) :
    Real.sin x * ∑ v ∈ range (N + 1), Real.cos (2 * v * x) =
        Real.cos (N * x) * Real.sin ((N + 1) * x) ∧
      Real.sin x * ∑ v ∈ range (N + 1), Real.sin (2 * v * x) =
        Real.sin (N * x) * Real.sin ((N + 1) * x) := by
  constructor
  · convert Real.sin_mul_sum_cos (N + 1) (2 * x) 0 using 1 <;>
      push_cast <;> ring_nf
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    ring
  · convert Real.sin_mul_sum_sin (N + 1) (2 * x) 0 using 1 <;>
      push_cast <;> ring_nf
    congr 1
    apply Finset.sum_congr rfl
    intro v _
    congr 1
    ring


private lemma fejer_mul_sin_sq (N : ℕ) (s : ℝ) :
    ((N : ℝ) + 1) * fejerKernel N s * Real.sin (Real.pi * s) ^ 2 =
      Real.sin ((N + 1) * (Real.pi * s)) ^ 2 := by
  obtain ⟨h1, h2⟩ := dirichlet_pair N (Real.pi * s)
  have ec : ∑ v ∈ range (N + 1), Real.cos (2 * Real.pi * v * s) =
      ∑ v ∈ range (N + 1), Real.cos (2 * v * (Real.pi * s)) :=
    sum_congr rfl fun v _ => by congr 1; ring
  have es : ∑ v ∈ range (N + 1), Real.sin (2 * Real.pi * v * s) =
      ∑ v ∈ range (N + 1), Real.sin (2 * v * (Real.pi * s)) :=
    sum_congr rfl fun v _ => by congr 1; ring
  rw [fejerKernel_sumsq, ec, es]
  set C := ∑ v ∈ range (N + 1), Real.cos (2 * v * (Real.pi * s))
  set S := ∑ v ∈ range (N + 1), Real.sin (2 * v * (Real.pi * s))
  set x := Real.pi * s
  linear_combination (Real.sin x * C + Real.cos (N * x) * Real.sin ((N + 1) * x)) * h1 +
    (Real.sin x * S + Real.sin (N * x) * Real.sin ((N + 1) * x)) * h2 +
    Real.sin ((N + 1) * x) ^ 2 * Real.cos_sq_add_sin_sq (N * x)

/-- `F_N(s) ≤ 1 / (4 (N+1) s²)` for `0 < |s| ≤ 1/2`. -/
lemma fejerKernel_le_inv_sq (N : ℕ) {s : ℝ} (hs0 : 0 < |s|) (hs : |s| ≤ 1 / 2) :
    fejerKernel N s ≤ 1 / (4 * (N + 1) * s ^ 2) := by
  have hN : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hF := fejerKernel_nonneg N s
  have hid := fejer_mul_sin_sq N s
  have hle1 : Real.sin ((N + 1) * (Real.pi * s)) ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]; exact Real.abs_sin_le_one _
  have hjordan : 4 * s ^ 2 ≤ Real.sin (Real.pi * s) ^ 2 := by
    have h0 : 0 ≤ Real.pi * |s| := by positivity
    have h1 : Real.pi * |s| ≤ Real.pi / 2 := by nlinarith [Real.pi_pos]
    have hj := Real.mul_le_sin h0 h1
    have e : 2 / Real.pi * (Real.pi * |s|) = 2 * |s| := by field_simp
    rw [e] at hj
    have e2 : Real.sin (Real.pi * s) ^ 2 = Real.sin (Real.pi * |s|) ^ 2 := by
      rcases abs_choice s with h | h <;> rw [h]
      simp [mul_neg, Real.sin_neg]
    rw [e2]
    have : (2 * |s|) ^ 2 = 4 * s ^ 2 := by rw [mul_pow, sq_abs]; ring
    rw [← this]
    exact pow_le_pow_left₀ (by positivity) hj 2
  have hsne : s ≠ 0 := abs_pos.mp hs0
  rw [le_div_iff₀ (by positivity)]
  calc fejerKernel N s * (4 * (N + 1) * s ^ 2) = (N + 1) * fejerKernel N s * (4 * s ^ 2) := by
        ring
    _ ≤ (N + 1) * fejerKernel N s * Real.sin (Real.pi * s) ^ 2 :=
        mul_le_mul_of_nonneg_left hjordan (by positivity)
    _ ≤ 1 := hid ▸ hle1

private def fejW (q ν : ℕ) : ℝ := 1 - (freq ν : ℝ) / (q + 1)

private lemma fejerKernel_expand (q : ℕ) (x t : ℝ) :
    fejerKernel q (x - t) =
      ∑ ν ∈ range (2 * q + 1), fejW q ν * fourierAtom ν x * fourierAtom ν t := by
  rw [sum_range_pair]
  unfold fejerKernel
  rw [mul_sum]
  congr 1
  · simp [fejW, freq, fourierAtom]
  · refine sum_congr rfl fun j hj => ?_
    obtain ⟨f1, f2⟩ := freq_spec (mem_Icc.1 hj).1
    have hp := fourierAtom_pair (mem_Icc.1 hj).1 x t
    simp only [fejW, f1, f2]
    linear_combination (-(1 - (j : ℝ) / (q + 1))) * hp

private lemma isTrigPoly_fejer (q : ℕ) {g : ℝ → ℝ} (hg : Continuous g) :
    IsTrigPoly q (fun x => ∫ t in (0 : ℝ)..1, g t * fejerKernel q (x - t)) := by
  refine ⟨fun ν => fejW q ν * ∫ t in (0 : ℝ)..1, g t * fourierAtom ν t, fun x => ?_⟩
  simp only [fejerKernel_expand, mul_sum]
  rw [intervalIntegral.integral_finsetSum
    (f := fun ν t => g t * (fejW q ν * fourierAtom ν x * fourierAtom ν t)) fun ν _ =>
    (hg.mul (continuous_const.mul (continuous_fourierAtom ν))).intervalIntegrable _ _]
  refine sum_congr rfl fun ν _ => ?_
  have e : (fun t => g t * (fejW q ν * fourierAtom ν x * fourierAtom ν t)) =
      fun t => (fejW q ν * fourierAtom ν x) * (g t * fourierAtom ν t) := by
    funext t; ring
  rw [e, intervalIntegral.integral_const_mul]
  ring

private lemma fejerKernel_neg (N : ℕ) (s : ℝ) : fejerKernel N (-s) = fejerKernel N s := by
  unfold fejerKernel
  simp [mul_neg, Real.cos_neg]

private lemma fejerKernel_periodic (N : ℕ) : Function.Periodic (fejerKernel N) 1 := by
  intro s
  unfold fejerKernel
  congr 2
  refine sum_congr rfl fun j _ => ?_
  rw [show 2 * Real.pi * j * (s + 1) = 2 * Real.pi * j * s + (j : ℕ) * (2 * Real.pi) by ring,
    Real.cos_add_nat_mul_two_pi]

/-- The moment integrand `|s|^α F_N(s)`. -/
private def momK (α : ℝ) (N : ℕ) (s : ℝ) : ℝ := |s| ^ α * fejerKernel N s

private lemma continuous_momK {α : ℝ} (hα : 0 < α) (N : ℕ) : Continuous (momK α N) :=
  ((Real.continuous_rpow_const hα.le).comp continuous_abs).mul (continuous_fejerKernel N)

private lemma momK_sym {α : ℝ} (hα : 0 < α) (N : ℕ) :
    ∫ s in (-1 / 2 : ℝ)..1 / 2, momK α N s = 2 * ∫ s in (0 : ℝ)..1 / 2, momK α N s := by
  have hi := fun a b => (continuous_momK hα N).intervalIntegrable (μ := volume) a b
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi (-1 / 2) 0) (hi 0 (1 / 2))]
  have : ∫ s in (-1 / 2 : ℝ)..0, momK α N s = ∫ s in (-1 / 2 : ℝ)..0, momK α N (-s) := by
    congr 1; funext s; simp [momK, abs_neg, fejerKernel_neg]
  rw [this, intervalIntegral.integral_comp_neg (fun s => momK α N s)]
  norm_num
  ring

private lemma momK_lower {α : ℝ} (hα : 0 < α) (N : ℕ) :
    ∫ s in (0 : ℝ)..1 / ((N : ℝ) + 1), momK α N s ≤ (1 / ((N : ℝ) + 1)) ^ α := by
  set δ := 1 / ((N : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hδN : δ * ((N : ℝ) + 1) = 1 := by rw [hδ]; field_simp
  have hle : ∫ s in (0 : ℝ)..δ, momK α N s ≤ ∫ _ in (0 : ℝ)..δ, ((N : ℝ) + 1) * δ ^ α := by
    apply intervalIntegral.integral_mono_on hδ0.le
      ((continuous_momK hα N).intervalIntegrable _ _) intervalIntegrable_const
    intro s hs
    unfold momK
    rw [abs_of_nonneg hs.1, mul_comm ((N : ℝ) + 1)]
    exact mul_le_mul (Real.rpow_le_rpow hs.1 hs.2 hα.le) (fejerKernel_le_succ N s)
      (fejerKernel_nonneg N s) (by positivity)
  rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero] at hle
  calc _ ≤ _ := hle
    _ = (δ * ((N : ℝ) + 1)) * δ ^ α := by ring
    _ = δ ^ α := by rw [hδN, one_mul]

private lemma momK_upper {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∫ s in (1 / ((N : ℝ) + 1))..1 / 2, momK α N s ≤ (1 / ((N : ℝ) + 1)) ^ α / (4 * (1 - α)) := by
  set δ := 1 / ((N : ℝ) + 1) with hδ
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hδ0 : 0 < δ := by positivity
  have hδN : δ * ((N : ℝ) + 1) = 1 := by rw [hδ]; field_simp
  have hδ2 : δ ≤ 1 / 2 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    rw [hδ, div_le_div_iff₀ hN1 (by norm_num)]
    linarith
  have hnot : (0 : ℝ) ∉ Set.uIcc δ (1 / 2) := by
    rw [Set.uIcc_of_le hδ2]; intro h; linarith [h.1]
  have hint : IntervalIntegrable (fun s : ℝ => s ^ (α - 2)) volume δ (1 / 2) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hnot)
  have hle : ∫ s in δ..1 / 2, momK α N s ≤ ∫ s in δ..1 / 2, s ^ (α - 2) / (4 * ((N : ℝ) + 1)) := by
    apply intervalIntegral.integral_mono_on hδ2 ((continuous_momK hα N).intervalIntegrable _ _)
      (hint.div_const _)
    intro s hs
    have hs0 : 0 < s := hδ0.trans_le hs.1
    have habs : 0 < |s| := abs_pos.mpr hs0.ne'
    have hs12 : |s| ≤ 1 / 2 := by rw [abs_of_pos hs0]; exact hs.2
    have hF := fejerKernel_le_inv_sq N habs hs12
    unfold momK
    rw [abs_of_pos hs0, Real.rpow_sub hs0, Real.rpow_two]
    calc s ^ α * fejerKernel N s ≤ s ^ α * (1 / (4 * (N + 1) * s ^ 2)) :=
          mul_le_mul_of_nonneg_left hF (by positivity)
      _ = s ^ α / s ^ 2 / (4 * ((N : ℝ) + 1)) := by field_simp
  rw [intervalIntegral.integral_div, integral_rpow (Or.inr ⟨by linarith, hnot⟩),
    show α - 2 + 1 = α - 1 by ring] at hle
  refine hle.trans ?_
  have hb : 0 ≤ (1 / 2 : ℝ) ^ (α - 1) := by positivity
  have hd : δ ^ (α - 1) = δ ^ α * ((N : ℝ) + 1) := by
    rw [Real.rpow_sub_one hδ0.ne', div_eq_iff hδ0.ne', mul_assoc, mul_comm ((N : ℝ) + 1), hδN,
      mul_one]
  have hα' : 0 < 1 - α := by linarith
  have e : ((1 / 2 : ℝ) ^ (α - 1) - δ ^ (α - 1)) / (α - 1) =
      (δ ^ (α - 1) - (1 / 2 : ℝ) ^ (α - 1)) / (1 - α) := by
    rw [← neg_sub (δ ^ (α - 1)), ← neg_sub 1 α, neg_div_neg_eq]
  rw [e, hd, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  have hpos : 0 ≤ (1 / 2 : ℝ) ^ (α - 1) * (4 * (1 - α)) := by positivity
  nlinarith

private lemma momK_le {α : ℝ} (hα : 0 < α) (hα1 : α < 1) {N : ℕ} (hN : 1 ≤ N) :
    ∫ s in (-1 / 2 : ℝ)..1 / 2, momK α N s ≤
      (2 + 1 / (2 * (1 - α))) * (1 / ((N : ℝ) + 1)) ^ α := by
  have hi := fun a b => (continuous_momK hα N).intervalIntegrable (μ := volume) a b
  rw [momK_sym hα, ← intervalIntegral.integral_add_adjacent_intervals (hi 0 (1 / ((N : ℝ) + 1)))
    (hi _ (1 / 2))]
  have h1 := momK_lower hα N
  have h2 := momK_upper hα hα1 hN
  have hα' : 0 < 1 - α := by linarith
  have e : 2 * ((1 / ((N : ℝ) + 1)) ^ α + (1 / ((N : ℝ) + 1)) ^ α / (4 * (1 - α))) =
      (2 + 1 / (2 * (1 - α))) * (1 / ((N : ℝ) + 1)) ^ α := by
    field_simp; ring
  rw [← e]
  linarith

private lemma fdiff_one_eq (h : ℝ) (g : ℝ → ℝ) (x : ℝ) : fdiff 1 h g x = g (x + h) - g x := by
  simp only [fdiff, Nat.reduceAdd, sum_range_succ, range_one, sum_singleton, tsub_zero,
    pow_one, Nat.choose_succ_self_right, zero_add, Nat.cast_one, mul_one,
    CharP.cast_eq_zero, zero_mul, add_zero, neg_mul, one_mul, tsub_self, pow_zero, Nat.choose_self]
  ring

private lemma jackson_error {α B : ℝ} (hα : 0 < α) {g : ℝ → ℝ} (hg : Continuous g)
    (hper : Function.Periodic g 1) (hB : 0 ≤ B)
    (hd : ∀ h x : ℝ, 0 < |h| → |h| ≤ 1 / 2 → |g (x + h) - g x| ≤ B * |h| ^ α) (N : ℕ) (x : ℝ) :
    |g x - ∫ t in (0 : ℝ)..1, g t * fejerKernel N (x - t)| ≤
      B * ∫ s in (-1 / 2 : ℝ)..1 / 2, momK α N s := by
  set φ : ℝ → ℝ := fun s => (g x - g (x - s)) * fejerKernel N s with hφ
  have hφc : Continuous φ :=
    (continuous_const.sub (hg.comp (continuous_const.sub continuous_id))).mul
      (continuous_fejerKernel N)
  have hφp : Function.Periodic φ 1 := by
    intro s
    simp only [hφ]
    rw [fejerKernel_periodic N s, show x - (s + 1) = (x - s) - 1 by ring, hper.sub_eq]
  have hc1 : Continuous fun t => g t * fejerKernel N (x - t) :=
    hg.mul ((continuous_fejerKernel N).comp (continuous_const.sub continuous_id))
  have hc2 : Continuous fun t => g x * fejerKernel N (x - t) :=
    continuous_const.mul ((continuous_fejerKernel N).comp (continuous_const.sub continuous_id))
  have e1 : g x = ∫ t in (0 : ℝ)..1, g x * fejerKernel N (x - t) := by
    rw [intervalIntegral.integral_const_mul, integral_fejerKernel_sub, mul_one]
  have e2 : ∫ t in (0 : ℝ)..1, φ (x - t) = ∫ s in (-1 / 2 : ℝ)..1 / 2, φ s := by
    rw [intervalIntegral.integral_comp_sub_left φ x, show x - 0 = (x - 1) + 1 by ring,
      hφp.intervalIntegral_add_eq (x - 1) (-1 / 2)]
    norm_num
  have hrep : g x - ∫ t in (0 : ℝ)..1, g t * fejerKernel N (x - t) =
      ∫ s in (-1 / 2 : ℝ)..1 / 2, φ s := by
    rw [← e2]
    conv_lhs => rw [e1]
    rw [← intervalIntegral.integral_sub (hc2.intervalIntegrable _ _) (hc1.intervalIntegrable _ _)]
    congr 1
    funext t
    simp only [hφ, sub_sub_cancel]
    ring
  rw [hrep]
  calc |∫ s in (-1 / 2 : ℝ)..1 / 2, φ s| ≤ ∫ s in (-1 / 2 : ℝ)..1 / 2, |φ s| :=
        intervalIntegral.abs_integral_le_integral_abs (by norm_num)
    _ ≤ ∫ s in (-1 / 2 : ℝ)..1 / 2, B * momK α N s := by
        apply intervalIntegral.integral_mono_on (by norm_num) (hφc.abs.intervalIntegrable _ _)
          (((continuous_momK hα N).const_mul B).intervalIntegrable _ _)
        intro s hs
        have hF := fejerKernel_nonneg N s
        simp only [hφ, momK]
        rw [abs_mul, abs_of_nonneg hF]
        by_cases hs0 : s = 0
        · rw [hs0, sub_zero, sub_self, abs_zero, zero_mul]
          exact mul_nonneg hB (mul_nonneg (by positivity) (fejerKernel_nonneg N 0))
        · have h1 : 0 < |-s| := by rw [abs_neg]; exact abs_pos.mpr hs0
          have h2 : |-s| ≤ 1 / 2 := by
            rw [abs_neg, abs_le]; constructor <;> linarith [hs.1, hs.2]
          have := hd (-s) x h1 h2
          rw [abs_neg, ← sub_eq_add_neg, abs_sub_comm] at this
          calc |g x - g (x - s)| * fejerKernel N s ≤ B * |s| ^ α * fejerKernel N s :=
                mul_le_mul_of_nonneg_right this hF
            _ = B * (|s| ^ α * fejerKernel N s) := by ring
    _ = B * ∫ s in (-1 / 2 : ℝ)..1 / 2, momK α N s := intervalIntegral.integral_const_mul _ _

/-- **Jackson inequality for `0 < α < 1` and first differences** (proved, not assumed). -/
theorem jackson_lip {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) : ∃ C : ℝ, JacksonIneq α 1 C := by
  refine ⟨2 + 1 / (2 * (1 - α)), fun R g hball q hq => ?_⟩
  obtain ⟨hg, hper, A, B, hA, hB, hAB, -, hdiff⟩ := hball
  have hd : ∀ h x : ℝ, 0 < |h| → |h| ≤ 1 / 2 → |g (x + h) - g x| ≤ B * |h| ^ α := by
    intro h x h1 h2
    have := hdiff h x h1 h2
    rwa [fdiff_one_eq] at this
  refine ⟨fun x => ∫ t in (0 : ℝ)..1, g t * fejerKernel q (x - t), isTrigPoly_fejer q hg,
    fun x => ?_⟩
  have h1 := jackson_error hα0 hg hper hB hd q x
  have h2 := momK_le hα0 hα1 hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have h3 : (1 / ((q : ℝ) + 1)) ^ α ≤ (q : ℝ) ^ (-α) := by
    rw [one_div, Real.inv_rpow (by positivity), ← Real.rpow_neg (by positivity)]
    exact Real.rpow_le_rpow_of_nonpos hq0 (by linarith) (by linarith)
  have hBR : B ≤ R := by linarith
  have hα' : 0 < 1 - α := by linarith
  have hC : 0 ≤ 2 + 1 / (2 * (1 - α)) := by positivity
  calc |g x - ∫ t in (0 : ℝ)..1, g t * fejerKernel q (x - t)|
      ≤ B * ((2 + 1 / (2 * (1 - α))) * (1 / ((q : ℝ) + 1)) ^ α) :=
        h1.trans (mul_le_mul_of_nonneg_left h2 hB)
    _ ≤ R * ((2 + 1 / (2 * (1 - α))) * (q : ℝ) ^ (-α)) := by
        apply mul_le_mul hBR (mul_le_mul_of_nonneg_left h3 hC) (by positivity) (hB.trans hBR)
    _ = (2 + 1 / (2 * (1 - α))) * R * (q : ℝ) ^ (-α) := by ring

private lemma atom_one_eq' (t : ℝ) :
    fourierAtom 1 t = Real.sqrt 2 * Real.cos (2 * Real.pi * t) := by
  simp [fourierAtom]

private lemma sqrt_two_mul_le {h : ℝ} (hh : |h| ≤ 1 / 2) :
    Real.sqrt 2 * |h| ≤ Real.sqrt |h| := by
  have ha := abs_nonneg h
  have e : Real.sqrt 2 * |h| = Real.sqrt (2 * |h|) * Real.sqrt |h| := by
    rw [Real.sqrt_mul (by norm_num), mul_assoc, Real.mul_self_sqrt ha]
  rw [e]
  have : Real.sqrt (2 * |h|) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  nlinarith [Real.sqrt_nonneg |h|, Real.sqrt_nonneg (2 * |h|)]

private lemma fdiff_one_atom_one_le (h t : ℝ) (hh : |h| ≤ 1 / 2) :
    |fdiff 1 h (fourierAtom 1) t| ≤ 2 * Real.pi * |h| ^ (1 / 2 : ℝ) := by
  have e : fdiff 1 h (fourierAtom 1) t = Real.sqrt 2 *
      (Real.cos (2 * Real.pi * (t + h)) - Real.cos (2 * Real.pi * t)) := by
    simp only [fdiff, Finset.sum_range_succ, Finset.sum_range_zero, atom_one_eq']
    norm_num
    ring
  have e2 : (2 * Real.pi * (t + h) - 2 * Real.pi * t) / 2 = Real.pi * h := by ring
  rw [e, Real.cos_sub_cos, e2, ← Real.sqrt_eq_rpow]
  have hsin : |Real.sin (Real.pi * h)| ≤ Real.pi * |h| := by
    have := Real.abs_sin_le_abs (x := Real.pi * h)
    rwa [abs_mul, abs_of_pos Real.pi_pos] at this
  have hs1 : |Real.sin ((2 * Real.pi * (t + h) + 2 * Real.pi * t) / 2)| ≤ 1 :=
    Real.abs_sin_le_one _
  have hk := sqrt_two_mul_le hh
  rw [abs_mul, abs_mul, abs_mul, abs_of_nonneg (Real.sqrt_nonneg 2), abs_neg, abs_two]
  have hpi := Real.pi_pos
  calc Real.sqrt 2 * (2 * |Real.sin ((2 * Real.pi * (t + h) + 2 * Real.pi * t) / 2)| *
        |Real.sin (Real.pi * h)|)
      ≤ Real.sqrt 2 * (2 * 1 * (Real.pi * |h|)) := by
        gcongr
    _ = 2 * Real.pi * (Real.sqrt 2 * |h|) := by ring
    _ ≤ 2 * Real.pi * Real.sqrt |h| := by gcongr

/-- `ψ₁` lies in the periodic Hölder–Zygmund ball of order `1/2`, difference order `1`, radius 8. -/
theorem corFourierHalf_nonvacuity :
    CorFourierHyp (d := 1) (fun _ => 1 / 2) (fun _ => 1) (fun _ => 1) 8 nvPsi1 1 (1 / 2) 1 := by
  exact
  { hd := one_pos
    hα := fun _ => by norm_num
    hr := fun _ => by norm_num
    hb := fun _ => by simp only [betaExp, alphaStar, Nat.cast_one, univ_unique, Fin.default_eq_zero,
      Fin.isValue, one_div, inv_inv, sum_const, card_singleton, one_smul, ne_eq,
      OfNat.ofNat_ne_zero, not_false_eq_true, mul_inv_cancel₀]; norm_num
    hball := by
      refine ⟨(continuous_fourierAtom 1).comp (continuous_apply 0), ?_, Real.sqrt 2,
        2 * Real.pi, Real.sqrt_nonneg 2, by positivity, ?_, fun x => fourierAtom_abs_le 1 (x 0), ?_⟩
      · intro k x
        obtain rfl : k = 0 := Subsingleton.elim k 0
        simp only [nvPsi1, Pi.add_apply, Pi.single_eq_same]
        exact fourierAtom_periodic 1 (x 0)
      · have : Real.sqrt 2 < 1.42 := by
          rw [Real.sqrt_lt' (by norm_num)]; norm_num
        have := Real.pi_lt_d2
        linarith
      · intro k x h _ hh
        obtain rfl : k = 0 := Subsingleton.elim k 0
        have hsec : sectionAt nvPsi1 x 0 = fourierAtom 1 := by
          funext t; simp [sectionAt, nvPsi1]
        rw [hsec]
        exact fdiff_one_atom_one_le h (x 0) hh
    hσ := one_pos
    hη := by norm_num
    hη1 := by norm_num
    hμ'' := one_pos }

/-- The Fourier end-to-end corollary for `f₀ = ψ₁` at smoothness `1/2`, with every hypothesis
proved, including the Jackson inequality (rate `(n/log n)^{−1/4}`). -/
theorem corFourier_instance_conclusion : ∃ Csp Ceps c5 : ℝ, 0 < Csp ∧ 0 < Ceps ∧ 0 ≤ c5 ∧
    CorConclusion (d := 1) (fun _ => 1 / 2) (fourierJ fun _ => 1)
      (fourierX (fun _ : Fin 1 => (1 : ℝ)) nvDesign) (fun n i => nvPsi1 (nvDesign n i)) 1
      (fun n => horseshoePDF (corTau 1 n (fourierJ (fun _ : Fin 1 => (1 : ℝ)) n))) Csp Ceps
      (1 / 2) (Aconst (Real.sqrt 2 ^ 1) (1 / 2) 1 (1 / 2) 1 c5) := by
  obtain ⟨C, hC⟩ := jackson_lip (α := 1 / 2) (by norm_num) (by norm_num)
  obtain ⟨Csp, Ceps, E, h1, h2, -, H⟩ := cor_fourier 1 (fun _ => 1 / 2) (fun _ => 1) (fun _ => C) 8
    (fun _ => hC) (fun _ => by norm_num) (fun _ => by norm_num)
  obtain ⟨c5, hc5, -, hconc⟩ := H (fun _ => 1) nvPsi1 nvDesign 1 (1 / 2) 1 (1 / 2)
    corFourierHalf_nonvacuity (by norm_num) (by norm_num)
  exact ⟨Csp, Ceps, c5, h1, h2, hc5, hconc⟩

end LargePrior
