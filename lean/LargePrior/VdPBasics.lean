import LargePrior.TrigBasics

/-!
# The de la Vallée Poussin smoother: definitions and algebra (blueprint §F.2)

`Qop m` is the budget-`m` smoother: for `m ≤ 2` it returns the mean `⟨g, ψ₀⟩`; for `m ≥ 3` it is
`V_q = 2σ_{2q−1} − σ_{q−1}` with `q = ⌊(m+1)/4⌋`, written directly in the real atoms (eq:vdp-real).
-/

open MeasureTheory Finset intervalIntegral
open scoped Real

noncomputable section

namespace LargePrior

/-- Coefficient integral `⟨g, ψ_ν⟩ = ∫₀¹ g ψ_ν`. -/
def coef (g : ℝ → ℝ) (ν : ℕ) : ℝ := ∫ t in (0 : ℝ)..1, g t * fourierAtom ν t

/-- de la Vallée Poussin multiplier `λ_j = 2(1 − j/(2q))₊ − (1 − j/q)₊`. -/
def vdpMult (q j : ℕ) : ℝ :=
  2 * max 0 (1 - (j : ℝ) / (2 * q)) - max 0 (1 - (j : ℝ) / q)

/-- Degree attached to a budget `m ≥ 3`: `q_m = ⌊(m+1)/4⌋`. -/
def budgetDeg (m : ℕ) : ℕ := (m + 1) / 4

/-- Multiplier of `Q_m` at frequency `j`: `λ_j` with `q = q_m` if `m ≥ 3`; `1_{j=0}` if `m ≤ 2`. -/
def qMult (m j : ℕ) : ℝ := if m ≤ 2 then (if j = 0 then 1 else 0) else vdpMult (budgetDeg m) j

/-- Number of atoms `Q_m` may output: `1` if `m ≤ 2`, else `4 q_m − 1` (atoms `ψ_0, …, ψ_{4q_m−2}`,
frequencies `≤ 2q_m − 1`). -/
def budgetAtoms (m : ℕ) : ℕ := if m ≤ 2 then 1 else 4 * budgetDeg m - 1

/-- The budget-`m` smoother `Q_m g = ∑_{ν < budgetAtoms m} Λ^{(m)}_{j(ν)} ⟨g, ψ_ν⟩ ψ_ν`. -/
def Qop (m : ℕ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ ν ∈ range (budgetAtoms m), qMult m (freq ν) * coef g ν * fourierAtom ν x

/-- Constant of the univariate error bound: `C'_α = max(4 · 8^α C, 2^{1+α})`. -/
def jackC' (α C : ℝ) : ℝ := max (4 * 8 ^ α * C) (2 ^ (1 + α))

/-! ### Helpers -/

/-- `0 ≤ 2 (1 − x/2)₊ − (1 − x)₊ ≤ 1` (for every real `x`). -/
private lemma vdp_real_mem_Icc (x : ℝ) :
    0 ≤ 2 * max 0 (1 - x / 2) - max 0 (1 - x) ∧ 2 * max 0 (1 - x / 2) - max 0 (1 - x) ≤ 1 := by
  rcases max_cases (0 : ℝ) (1 - x / 2) with ⟨h1, h1'⟩ | ⟨h1, h1'⟩ <;>
    rcases max_cases (0 : ℝ) (1 - x) with ⟨h2, h2'⟩ | ⟨h2, h2'⟩ <;>
    · rw [h1, h2]; constructor <;> linarith

private lemma vdpMult_eq (q j : ℕ) :
    vdpMult q j = 2 * max 0 (1 - ((j : ℝ) / q) / 2) - max 0 (1 - (j : ℝ) / q) := by
  unfold vdpMult
  congr 3
  ring

private lemma vdpMult_mem_Icc (q j : ℕ) : 0 ≤ vdpMult q j ∧ vdpMult q j ≤ 1 := by
  rw [vdpMult_eq]
  exact vdp_real_mem_Icc _

private lemma vdpMult_eq_one {q j : ℕ} (hjq : j ≤ q) : vdpMult q j = 1 := by
  rw [vdpMult_eq]
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    norm_num
  · have hq' : (0 : ℝ) < q := by exact_mod_cast hq
    have hx : (j : ℝ) / q ≤ 1 := by
      rw [div_le_one hq']; exact_mod_cast hjq
    have hx0 : 0 ≤ (j : ℝ) / q := by positivity
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    ring

private lemma coef_sub {g p : ℝ → ℝ} (hg : Continuous g) (hp : Continuous p) (ν : ℕ) :
    coef (g - p) ν = coef g ν - coef p ν := by
  unfold coef
  have hψ := continuous_fourierAtom ν
  simp only [Pi.sub_apply, sub_mul]
  exact intervalIntegral.integral_sub ((hg.mul hψ).intervalIntegrable _ _)
    ((hp.mul hψ).intervalIntegrable _ _)

private lemma coef_const_mul (c : ℝ) (g : ℝ → ℝ) (ν : ℕ) :
    coef (fun t => c * g t) ν = c * coef g ν := by
  unfold coef
  simp only [mul_assoc]
  exact intervalIntegral.integral_const_mul _ _

private lemma coef_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℝ)
    (hg : ∀ i ∈ s, Continuous (g i)) (ν : ℕ) :
    coef (fun t => ∑ i ∈ s, g i t) ν = ∑ i ∈ s, coef (g i) ν := by
  unfold coef
  simp only [Finset.sum_mul]
  exact intervalIntegral.integral_finsetSum fun i hi =>
    ((hg i hi).mul (continuous_fourierAtom ν)).intervalIntegrable _ _

/-- Coefficients of a trigonometric polynomial, by orthonormality. -/
private lemma coef_trigPoly {q : ℕ} {p : ℝ → ℝ} {c : ℕ → ℝ}
    (hp : ∀ x, p x = ∑ ν ∈ range (2 * q + 1), c ν * fourierAtom ν x) (μ : ℕ) :
    coef p μ = if μ ∈ range (2 * q + 1) then c μ else 0 := by
  unfold coef
  simp only [hp, Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum
    (f := fun ν t => c ν * fourierAtom ν t * fourierAtom μ t) fun ν _ =>
    ((continuous_const.mul (continuous_fourierAtom ν)).mul
      (continuous_fourierAtom μ)).intervalIntegrable _ _]
  simp only [mul_assoc, intervalIntegral.integral_const_mul, integral_fourierAtom_mul,
    mul_ite, mul_one, mul_zero]
  exact Finset.sum_ite_eq' _ _ _

/-- `0 ≤ Λ^{(m)}_j ≤ 1` (eq:vdp-multipliers). -/
lemma qMult_mem_Icc (m j : ℕ) : 0 ≤ qMult m j ∧ qMult m j ≤ 1 := by
  unfold qMult
  split_ifs
  · norm_num
  · norm_num
  · exact vdpMult_mem_Icc _ _

/-- Atom count (eq:atom-count): `budgetAtoms m ≤ m` for `m ≥ 1`. -/
lemma budgetAtoms_le {m : ℕ} (hm : 1 ≤ m) : budgetAtoms m ≤ m := by
  unfold budgetAtoms budgetDeg
  split_ifs <;> omega

/-- `|⟨g, ψ_ν⟩| ≤ A` when `g` is continuous and `|g| ≤ A`. -/
lemma coef_abs_le {g : ℝ → ℝ} {A : ℝ} (hg : Continuous g) (hA : ∀ t, |g t| ≤ A) (ν : ℕ) :
    |coef g ν| ≤ A := by
  have hA0 : 0 ≤ A := (abs_nonneg _).trans (hA 0)
  have hψ := continuous_fourierAtom ν
  unfold coef
  calc |∫ t in (0 : ℝ)..1, g t * fourierAtom ν t|
      ≤ ∫ t in (0 : ℝ)..1, |g t * fourierAtom ν t| :=
        intervalIntegral.abs_integral_le_integral_abs zero_le_one
    _ ≤ ∫ t in (0 : ℝ)..1, A * |fourierAtom ν t| := by
        refine intervalIntegral.integral_mono_on zero_le_one
          ((hg.mul hψ).abs.intervalIntegrable _ _)
          ((continuous_const.mul hψ.abs).intervalIntegrable _ _) fun t _ => ?_
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_right (hA t) (abs_nonneg _)
    _ = A * ∫ t in (0 : ℝ)..1, |fourierAtom ν t| := intervalIntegral.integral_const_mul _ _
    _ ≤ A * 1 := mul_le_mul_of_nonneg_left (integral_abs_fourierAtom_le ν) hA0
    _ = A := mul_one A

/-- Linearity: `Q_m (g − p) = Q_m g − Q_m p` for continuous `g, p`. -/
lemma Qop_sub {g p : ℝ → ℝ} (hg : Continuous g) (hp : Continuous p) (m : ℕ) (x : ℝ) :
    Qop m (g - p) x = Qop m g x - Qop m p x := by
  unfold Qop
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coef_sub hg hp]
  ring

/-- Reproduction (eq:vdp-eigen): for `m ≥ 3`, `Q_m p = p` for every trigonometric polynomial of
degree at most `q_m`. -/
lemma Qop_trigPoly {m q : ℕ} {p : ℝ → ℝ} (hm : 3 ≤ m) (hq : q ≤ budgetDeg m)
    (hp : IsTrigPoly q p) (x : ℝ) : Qop m p x = p x := by
  obtain ⟨c, hc⟩ := hp
  have hm' : ¬ m ≤ 2 := by omega
  have hdeg : 1 ≤ budgetDeg m := by unfold budgetDeg; omega
  have hsub : range (2 * q + 1) ⊆ range (budgetAtoms m) := by
    intro ν hν
    simp only [Finset.mem_range, budgetAtoms, hm', ↓reduceIte] at hν ⊢
    omega
  unfold Qop
  rw [hc x]
  symm
  refine Finset.sum_subset_zero_on_sdiff hsub (fun ν hν => ?_) (fun ν hν => ?_)
  · rw [Finset.mem_sdiff] at hν
    rw [coef_trigPoly hc]
    simp only [hν.2, ↓reduceIte]
    ring
  · have hfreq : freq ν ≤ budgetDeg m := by
      rw [Finset.mem_range] at hν
      unfold freq; omega
    rw [coef_trigPoly hc, qMult]
    simp only [hν, hm', ↓reduceIte, vdpMult_eq_one hfreq]
    ring

/-- For `m ≥ 3`: `1 ≤ q_m` and `m/8 ≤ q_m`. -/
lemma budgetDeg_bounds {m : ℕ} (hm : 3 ≤ m) : 1 ≤ budgetDeg m ∧ (m : ℝ) / 8 ≤ budgetDeg m := by
  refine ⟨by unfold budgetDeg; omega, ?_⟩
  have h : m ≤ 8 * budgetDeg m := by unfold budgetDeg; omega
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 8)]
  have h' : (m : ℝ) ≤ ((8 * budgetDeg m : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- Homogeneity: `Q_m (c · g) = c · Q_m g`. -/
lemma Qop_const_mul (m : ℕ) (c : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    Qop m (fun t => c * g t) x = c * Qop m g x := by
  unfold Qop
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [coef_const_mul]
  ring

/-- Additivity over finite sums of continuous functions. -/
lemma Qop_finset_sum {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℝ) (hg : ∀ i ∈ s, Continuous (g i))
    (m : ℕ) (x : ℝ) : Qop m (fun t => ∑ i ∈ s, g i t) x = ∑ i ∈ s, Qop m (g i) x := by
  unfold Qop
  simp only [coef_finset_sum s g hg, Finset.mul_sum, Finset.sum_mul]
  exact Finset.sum_comm

end LargePrior
