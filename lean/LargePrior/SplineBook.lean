import LargePrior.CorSpec

/-!
# Spline levels (`eq:nearest-spline-level`)
-/

open Finset

noncomputable section

namespace LargePrior

/-- Level chosen for a budget `m` (truncation `H`): `0` if `m < q = D_0`, otherwise the largest
`ℓ ≤ H` with `D_ℓ ≤ m` (this is `H` when `m > D_H`). -/
def splineLevel (q H m : ℕ) : ℕ :=
  if m < q then 0 else Nat.findGreatest (fun ℓ => splineDim q ℓ ≤ m) H

lemma splineLevel_le (q H m : ℕ) : splineLevel q H m ≤ H := by
  unfold splineLevel
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.findGreatest_le H

lemma one_le_splineDim {q : ℕ} (hq : 1 ≤ q) (ℓ : ℕ) : 1 ≤ splineDim q ℓ := by
  unfold splineDim
  have := Nat.one_le_two_pow (n := ℓ)
  omega

private lemma splineDim_zero (q : ℕ) : splineDim q 0 = q := by
  unfold splineDim
  simp

private lemma splineDim_succ_le {q : ℕ} (hq : 1 ≤ q) (ℓ : ℕ) :
    splineDim q (ℓ + 1) ≤ 2 * splineDim q ℓ := by
  unfold splineDim
  rw [pow_succ]
  omega

private lemma splineUnionDim_le {q : ℕ} (hq : 1 ≤ q) (H : ℕ) :
    splineUnionDim q H ≤ 2 * q * splineDim q H := by
  induction H with
  | zero =>
    unfold splineUnionDim
    rw [Finset.sum_range_one, splineDim_zero]
    nlinarith
  | succ H ih =>
    have hs : splineUnionDim q (H + 1) = splineUnionDim q H + splineDim q (H + 1) := by
      unfold splineUnionDim
      rw [Finset.sum_range_succ]
    rw [hs]
    obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by omega⟩
    have h2 : 1 ≤ 2 ^ H := Nat.one_le_two_pow
    have hd1 : splineDim (r + 1) H = 2 ^ H + r := by unfold splineDim; omega
    have hd2 : splineDim (r + 1) (H + 1) = 2 * 2 ^ H + r := by
      unfold splineDim; rw [pow_succ]; omega
    rw [hd1] at ih
    rw [hd2]
    nlinarith [Nat.zero_le (r * 2 ^ H), Nat.zero_le r]

/-- (eq:nearest-spline-level): for `1 ≤ m ≤ U_H`, `m/(2q) ≤ D_{ℓ_H(m)} ≤ q m`. -/
lemma splineLevel_bounds {q H m : ℕ} (hq : 1 ≤ q) (hm1 : 1 ≤ m)
    (hmU : m ≤ splineUnionDim q H) :
    (m : ℝ) / (2 * q) ≤ splineDim q (splineLevel q H m) ∧
      (splineDim q (splineLevel q H m) : ℝ) ≤ q * m := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm1
  have hq0 : (0 : ℝ) < 2 * q := by linarith
  by_cases hmq : m < q
  · have hl : splineLevel q H m = 0 := by simp [splineLevel, hmq]
    rw [hl, splineDim_zero]
    have hmqR : (m : ℝ) < q := by exact_mod_cast hmq
    refine ⟨?_, by nlinarith⟩
    rw [div_le_iff₀ hq0]
    nlinarith
  · push Not at hmq
    have hl : splineLevel q H m = Nat.findGreatest (fun ℓ => splineDim q ℓ ≤ m) H := by
      simp [splineLevel, not_lt.mpr hmq]
    rw [hl]
    set L := Nat.findGreatest (fun ℓ => splineDim q ℓ ≤ m) H with hL
    have hspec : splineDim q L ≤ m := by
      have h0 : (fun ℓ => splineDim q ℓ ≤ m) 0 := by
        show splineDim q 0 ≤ m
        rw [splineDim_zero]; exact hmq
      exact Nat.findGreatest_spec (P := fun ℓ => splineDim q ℓ ≤ m) (Nat.zero_le H) h0
    have hspecR : (splineDim q L : ℝ) ≤ m := by exact_mod_cast hspec
    refine ⟨?_, by nlinarith⟩
    rw [div_le_iff₀ hq0]
    have hDpos : (1 : ℝ) ≤ splineDim q L := by exact_mod_cast one_le_splineDim hq L
    have key : m ≤ 2 * q * splineDim q L := by
      rcases Nat.lt_or_ge L H with hLH | hLH
      · have hn : ¬ splineDim q (L + 1) ≤ m :=
          Nat.findGreatest_is_greatest (P := fun ℓ => splineDim q ℓ ≤ m) (Nat.lt_succ_self L) hLH
        have h2 := splineDim_succ_le hq L
        have h3 : 1 ≤ splineDim q L := one_le_splineDim hq L
        nlinarith
      · have hLH' : L = H := le_antisymm (Nat.findGreatest_le H) hLH
        have hU : m ≤ splineUnionDim q H := hmU
        rw [hLH']
        exact hU.trans (splineUnionDim_le hq H)
    have keyR : (m : ℝ) ≤ 2 * q * splineDim q L := by exact_mod_cast key
    linarith

/-- From `D ≥ m/(2q)`: `D^{−α} ≤ (2q)^α m^{−α}`, for `α > 0`, `m ≥ 1`. -/
lemma rpow_neg_le_of_level {q m D : ℕ} {α : ℝ} (hq : 1 ≤ q) (hm : 1 ≤ m) (hα : 0 < α)
    (hD : (m : ℝ) / (2 * q) ≤ D) :
    (D : ℝ) ^ (-α) ≤ (2 * q : ℝ) ^ α * (m : ℝ) ^ (-α) := by
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hq0 : (0 : ℝ) < 2 * q := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hpos : (0 : ℝ) < (m : ℝ) / (2 * q) := div_pos hm0 hq0
  have h1 : ((D : ℝ)) ^ (-α) ≤ ((m : ℝ) / (2 * q)) ^ (-α) :=
    Real.rpow_le_rpow_of_nonpos hpos hD (by linarith)
  have h2 : ((m : ℝ) / (2 * q)) ^ (-α) = (2 * q : ℝ) ^ α * (m : ℝ) ^ (-α) := by
    rw [Real.div_rpow hm0.le hq0.le, Real.rpow_neg hm0.le, Real.rpow_neg hq0.le]
    field_simp
  rw [← h2]
  exact h1

/-- `D^{−α} ≤ 1` for `D ≥ 1`, `α > 0`. -/
lemma rpow_neg_le_one_of_one_le {D : ℕ} {α : ℝ} (hD : 1 ≤ D) (hα : 0 < α) :
    (D : ℝ) ^ (-α) ≤ 1 := by
  have hD' : (1 : ℝ) ≤ D := by exact_mod_cast hD
  exact Real.rpow_le_one_of_one_le_of_nonpos hD' (by linarith)

end LargePrior
