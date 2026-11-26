import LargePrior.Spec

/-!
# (WG5): the Lean form and the paper's form

The paper states (WG5) as `a_n [log a_n + 2 log(1/ε̃_n) − log π_inf] ≤ c₅ n ε̃_n²` with
`π_inf = inf_{|t| ≤ E_n} π_n(t) > 0` and `c₅ ≥ 0`, without a positive part. The Lean `WG5` uses
an almost-everywhere lower bound `π_low` and the positive part `[·]_+`. Since `c₅ ≥ 0`, the
positive part changes nothing (`wg5_iff_noPos`), and the paper's form implies the Lean form
(`wg5Paper_implies_wg5`), so every theorem assuming `WG5` applies under the paper's (WG5).
-/

open MeasureTheory

noncomputable section

namespace LargePrior

/-- (WG5) with an almost-everywhere lower bound and without the positive part. -/
def WG5NoPos (pdf : ℝ → ℝ) (E εt c5 : ℝ) (a n : ℕ) : Prop :=
  ∃ πlow : ℝ, 0 < πlow ∧ (∀ᵐ t ∂volume, |t| ≤ E → πlow ≤ pdf t) ∧
    (a : ℝ) * (Real.log a + 2 * Real.log (1 / εt) - Real.log πlow) ≤ c5 * n * εt ^ 2

/-- For `c₅ ≥ 0` the positive part in `WG5` is immaterial. -/
theorem wg5_iff_noPos {pdf : ℝ → ℝ} {E εt c5 : ℝ} {a n : ℕ}
    (hc5 : 0 ≤ c5) : WG5 pdf E εt c5 a n ↔ WG5NoPos pdf E εt c5 a n := by
  have hR : 0 ≤ c5 * n * εt ^ 2 :=
    mul_nonneg (mul_nonneg hc5 (Nat.cast_nonneg n)) (sq_nonneg εt)
  constructor
  · rintro ⟨πlow, hp, hlower, hbound⟩
    exact ⟨πlow, hp, hlower,
      (mul_le_mul_of_nonneg_left (le_max_right 0 _) (Nat.cast_nonneg a)).trans hbound⟩
  · rintro ⟨πlow, hp, hlower, hbound⟩
    refine ⟨πlow, hp, hlower, ?_⟩
    rw [mul_max_of_nonneg _ _ (Nat.cast_nonneg a), mul_zero]
    exact max_le hR hbound

/-- The paper's (WG5): `π_inf = inf_{|t| ≤ E} π(t) > 0` (the real infimum of the pointwise
values on `[−E, E]`) and `a [log a + 2 log(1/ε̃) − log π_inf] ≤ c₅ n ε̃²`. -/
def WG5Paper (pdf : ℝ → ℝ) (E εt c5 : ℝ) (a n : ℕ) : Prop :=
  0 < sInf (pdf '' Set.Icc (-E) E) ∧
    (a : ℝ) * (Real.log a + 2 * Real.log (1 / εt) -
      Real.log (sInf (pdf '' Set.Icc (-E) E))) ≤ c5 * n * εt ^ 2

/-- **The paper's (WG5) implies the Lean `WG5`** (for `c₅ ≥ 0` and `π` bounded below on
`[−E, E]`, automatic for a density since `π ≥ 0`): take `π_low = π_inf`. -/
theorem wg5Paper_implies_wg5 {pdf : ℝ → ℝ} {E εt c5 : ℝ} {a n : ℕ}
    (hc5 : 0 ≤ c5) (hbelow : BddBelow (pdf '' Set.Icc (-E) E))
    (hpaper : WG5Paper pdf E εt c5 a n) : WG5 pdf E εt c5 a n := by
  apply (wg5_iff_noPos hc5).mpr
  refine ⟨sInf (pdf '' Set.Icc (-E) E), hpaper.1, ?_, hpaper.2⟩
  exact Filter.Eventually.of_forall fun t ht => csInf_le hbelow ⟨t, abs_le.mp ht, rfl⟩

end LargePrior
