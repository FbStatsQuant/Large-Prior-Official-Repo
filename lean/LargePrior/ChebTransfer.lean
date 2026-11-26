import LargePrior.ChebSpec

/-!
# LargePrior: the smoothness transfer for the Chebyshev fold (L-02, Lane A)

The transfer `f ↦ f ∘ chebFold` from `C^α([0,1])` into the periodic Hölder–Zygmund ball of radius
`C_tr(α) R` (eq:cheb-transfer, D:538–554).

* `cheb_transfer_le_one` (T1): the case `0 < α ≤ 1` (`s = 0`, `β = α`).
* Fold lemmas `*_tr`: range, period 1, `π`-Lipschitz bound and smoothness.
* Forward differences: `fdiff_eq_fwdDiff_iter` and the doubling bound `abs_fwdDiff_iter_le`.

The explicit fold derivatives, the within-derivative chain rule and the Bell-recurrence bound
for the general case `s ≥ 1` are in `ChebTransferHigh`.
-/

open Real
open scoped ContDiff

noncomputable section

namespace LargePrior

/-! ## The fold: range, periodicity, Lipschitz bound

Transfer-specific names (suffix `_tr`), so as not to clash with the public fold facts of
`ChebBasis`. -/

theorem chebFold_mem_Icc_tr (u : ℝ) : chebFold u ∈ Set.Icc (0 : ℝ) 1 := by
  have h1 := Real.neg_one_le_cos (2 * π * u)
  have h2 := Real.cos_le_one (2 * π * u)
  unfold chebFold
  constructor <;> linarith

theorem chebFold_periodic_tr : Function.Periodic chebFold 1 := by
  intro u
  unfold chebFold
  rw [show 2 * π * (u + 1) = 2 * π * u + 2 * π by ring, Real.cos_add_two_pi]

/-- `|x(u) − x(v)| ≤ π |u − v|` (eq:cheb-fold-bounds). -/
theorem abs_chebFold_sub_le_tr (u v : ℝ) : |chebFold u - chebFold v| ≤ π * |u - v| := by
  have h := Real.abs_cos_sub_cos_le (2 * π * u) (2 * π * v)
  rw [show 2 * π * u - 2 * π * v = (2 * π) * (u - v) by ring, abs_mul,
    abs_of_pos (by positivity : (0 : ℝ) < 2 * π)] at h
  unfold chebFold
  rw [show (1 + Real.cos (2 * π * u)) / 2 - (1 + Real.cos (2 * π * v)) / 2 =
      (Real.cos (2 * π * u) - Real.cos (2 * π * v)) / 2 by ring, abs_div, abs_two]
  linarith

theorem chebFold_contDiff_tr : ContDiff ℝ ∞ chebFold :=
  (contDiff_const.add (Real.contDiff_cos.comp (contDiff_const.mul contDiff_id))).div_const 2

/-! ## Forward differences -/

/-- The explicit `r`-th difference `fdiff` of `CorSpec` is the `r`-fold iterate of `fwdDiff`. -/
theorem fdiff_eq_fwdDiff_iter (r : ℕ) (h : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    fdiff r h g x = (fwdDiff h)^[r] g x := by
  rw [fwdDiff_iter_eq_sum_shift]
  unfold fdiff
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [zsmul_eq_mul, nsmul_eq_mul]
  push_cast
  ring

/-- Each difference at most doubles the sup bound: `|Δ_h^n φ| ≤ 2^n M` if `|φ| ≤ M`. -/
theorem abs_fwdDiff_iter_le (h : ℝ) (n : ℕ) :
    ∀ (φ : ℝ → ℝ) (M : ℝ), (∀ y, |φ y| ≤ M) → ∀ y, |(fwdDiff h)^[n] φ y| ≤ 2 ^ n * M := by
  induction n with
  | zero => intro φ M hφ y; simpa using hφ y
  | succ n ih =>
    intro φ M hφ y
    have h1 : ∀ z, |fwdDiff h φ z| ≤ 2 * M := by
      intro z
      calc |fwdDiff h φ z| = |φ (z + h) + -φ z| := by rw [fwdDiff, sub_eq_add_neg]
        _ ≤ |φ (z + h)| + |-φ z| := abs_add_le _ _
        _ ≤ M + M := by rw [abs_neg]; exact add_le_add (hφ _) (hφ _)
        _ = 2 * M := by ring
    calc |(fwdDiff h)^[n + 1] φ y| = |(fwdDiff h)^[n] (fwdDiff h φ) y| := rfl
      _ ≤ 2 ^ n * (2 * M) := ih _ _ h1 y
      _ = 2 ^ (n + 1) * M := by ring

/-! ## T1: the transfer for `0 < α ≤ 1` -/

theorem chebS_of_le_one {α : ℝ} (hα1 : α ≤ 1) : chebS α = 0 := by
  have : ⌈α⌉₊ ≤ 1 := Nat.ceil_le.mpr (by exact_mod_cast hα1)
  unfold chebS
  omega

theorem chebBeta_of_le_one {α : ℝ} (hα1 : α ≤ 1) : chebBeta α = α := by
  simp [chebBeta, chebS_of_le_one hα1]

theorem chebCtr_of_le_one {α : ℝ} (r : ℕ) (hα1 : α ≤ 1) :
    chebCtr α r = 1 + 2 ^ (r - 1) * π ^ α := by
  simp [chebCtr, chebKappa, chebS_of_le_one hα1, chebBeta_of_le_one hα1]

/-- **T1: the smoothness transfer for `0 < α ≤ 1`** (D:536–538 with `s = 0`, then D:552). Here
`|Δ_h g| ≤ R |x(u+h) − x(u)|^α ≤ π^α R |h|^α`, and the other `r − 1` differences at most double
the sup bound, so `A = R` and `B = 2^{r−1} π^α R`. -/
theorem cheb_transfer_le_one {α : ℝ} {r : ℕ} (hα : 0 < α) (hα1 : α ≤ 1) (hr : α < r) :
    ChebTransferPremise α r := by
  intro R f hf
  obtain ⟨hcont, hbd, hhol⟩ := hf
  have hs := chebS_of_le_one hα1
  have hb := chebBeta_of_le_one hα1
  have hsup : ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ R := by
    intro y hy
    simpa using hbd 0 (Nat.zero_le _) y hy
  have hhol' : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1, |f y - f z| ≤ R * |y - z| ^ α := by
    simpa only [hs, hb, iteratedDerivWithin_zero] using hhol
  have hR : 0 ≤ R := (abs_nonneg _).trans (hsup 0 (Set.left_mem_Icc.mpr zero_le_one))
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := by
    refine ⟨r - 1, ?_⟩
    have : r ≠ 0 := by
      rintro rfl
      norm_num at hr
      linarith
    omega
  refine ⟨hcont.continuousOn.comp_continuous chebFold_contDiff_tr.continuous chebFold_mem_Icc_tr,
    fun u => by simp only [Function.comp_apply, chebFold_periodic_tr u],
    R, 2 ^ n * π ^ α * R, hR, by positivity, ?_, fun u => hsup _ (chebFold_mem_Icc_tr u), ?_⟩
  · rw [chebCtr_of_le_one _ hα1, Nat.add_sub_cancel]
    ring_nf
    exact le_rfl
  · intro h y _ _
    have hΔ : ∀ z, |fwdDiff h (f ∘ chebFold) z| ≤ π ^ α * R * |h| ^ α := by
      intro z
      have hlip : |chebFold (z + h) - chebFold z| ≤ π * |h| := by
        simpa using abs_chebFold_sub_le_tr (z + h) z
      calc |fwdDiff h (f ∘ chebFold) z| = |f (chebFold (z + h)) - f (chebFold z)| := rfl
        _ ≤ R * |chebFold (z + h) - chebFold z| ^ α :=
          hhol' _ (chebFold_mem_Icc_tr _) _ (chebFold_mem_Icc_tr _)
        _ ≤ R * (π * |h|) ^ α :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hlip hα.le) hR
        _ = π ^ α * R * |h| ^ α := by
          rw [Real.mul_rpow Real.pi_pos.le (abs_nonneg h)]
          ring
    rw [fdiff_eq_fwdDiff_iter]
    calc |(fwdDiff h)^[n + 1] (f ∘ chebFold) y|
        = |(fwdDiff h)^[n] (fwdDiff h (f ∘ chebFold)) y| := rfl
      _ ≤ 2 ^ n * (π ^ α * R * |h| ^ α) := abs_fwdDiff_iter_le h n _ _ hΔ y
      _ = 2 ^ n * π ^ α * R * |h| ^ α := by ring

end LargePrior
