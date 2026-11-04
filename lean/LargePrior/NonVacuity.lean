import LargePrior.HorseshoeMain
import LargePrior.Basis

/-!
# Non-vacuity (blueprint `prop:nonvacuity`)

A concrete instance satisfying every hypothesis of `MainHorseshoeStatement`: the univariate
Fourier dictionary `ψ₀, …, ψ_{n+1}` at the design `xᵢ = i/n`, the truth `f₀ = ψ₁`, `σ = 1`,
`ε̃_n = (n+1)^{−1/4}`, `δ_n = ε̃_n / J_n`, the horseshoe with `τ_n = J_n^{−3}/√n`, `M_n = log(n+2)`.
`nonvacuity` states that this instance satisfies every hypothesis of `main_horseshoe`; proving it
checks each hypothesis, so the hypotheses are not contradictory.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

/-- `J_n = n + 2`. -/
def nvJ (n : ℕ) : ℕ := n + 2

/-- Fourier design matrix: atom `j` is `ψ_j`, evaluated at `xᵢ = i/n`. -/
def nvX (n : ℕ) : Matrix (Fin n) (Fin (nvJ n)) ℝ :=
  designMatrix (fun j : Fin (nvJ n) => fourierTensor (d := 1) (fun _ => (j : ℕ)))
    (fun i : Fin n => fun _ => (i : ℝ) / n)

/-- The truth `f₀ = ψ₁` at the design points. -/
def nvf₀ (n : ℕ) : Fin n → ℝ := fun i => fourierAtom 1 ((i : ℝ) / n)

/-- `ε̃_n = (n + 1)^{−1/4}`. -/
def nvεt (n : ℕ) : ℝ := ((n : ℝ) + 1) ^ (-(1 / 4 : ℝ))

/-- `δ_n = ε̃_n / J_n`. -/
def nvδ (n : ℕ) : ℝ := nvεt n / nvJ n

/-- `τ_n = J_n^{−3} / √n` for `n ≥ 1` (and `1` at `n = 0`). -/
def nvτ (n : ℕ) : ℝ := if n = 0 then 1 else ((nvJ n : ℕ) : ℝ) ^ (-(3 : ℝ)) / Real.sqrt n

/-- `M_n = log(n + 2)` (so that `M_n ε_n → 0`: the witnessed conclusion is about shrinking balls). -/
def nvM (n : ℕ) : ℝ := Real.log ((n : ℝ) + 2)

/-- `E_n = 1`. -/
def nvE (_n : ℕ) : ℝ := 1

/-- `a_n = 1`. -/
def nva (_n : ℕ) : ℕ := 1


/-! ### Helper lemmas for `nonvacuity` -/

private lemma nvεt_pos (n : ℕ) : 0 < nvεt n := by
  unfold nvεt; positivity

private lemma nvεt_sq (n : ℕ) : nvεt n ^ 2 = 1 / Real.sqrt ((n : ℝ) + 1) := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  unfold nvεt
  rw [← Real.rpow_natCast, ← Real.rpow_mul hpos.le,
    show (-(1 / 4 : ℝ)) * ((2 : ℕ) : ℝ) = -(1 / 2) by norm_num, Real.rpow_neg hpos.le,
    Real.sqrt_eq_rpow, inv_eq_one_div]

private lemma log_le_two_sqrt {x : ℝ} (hx : 0 < x) : Real.log x ≤ 2 * Real.sqrt x := by
  have h1 := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 hx)
  rw [Real.log_sqrt hx.le] at h1
  linarith

private lemma nvJ_cast (n : ℕ) : ((nvJ n : ℕ) : ℝ) = (n : ℝ) + 2 := by
  simp [nvJ]

private lemma nv_hnεt : Tendsto (fun n : ℕ => (n : ℝ) * nvεt n ^ 2) atTop atTop := by
  have hq : Tendsto (fun n : ℕ => Real.sqrt ((n : ℝ) + 1) + (-1)) atTop atTop :=
    tendsto_atTop_add_const_right _ _ (Real.tendsto_sqrt_atTop.comp
      (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop))
  refine tendsto_atTop_mono (fun n => ?_) hq
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hq1 : 1 ≤ Real.sqrt ((n : ℝ) + 1) := by
    rw [Real.one_le_sqrt]; linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
  have hsq := Real.sq_sqrt hpos.le
  rw [nvεt_sq, mul_one_div, le_div_iff₀ (by linarith)]
  nlinarith

private lemma nv_hs_bound {n : ℕ} (hn : 1 ≤ n) :
    (sRate n (nvJ n) (nva n) (nvεt n) : ℝ) * Real.log (nvJ n) / n ≤ 5 / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hJ := nvJ_cast n
  have hr : 0 < Real.sqrt n := Real.sqrt_pos.2 hn0
  have hr2 : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hn0.le
  have hL : 0 < Real.log ((n : ℝ) + 2) := Real.log_pos (by linarith)
  have hLle : Real.log ((n : ℝ) + 2) ≤ 4 * Real.sqrt n := by
    have h1 := log_le_two_sqrt (x := (n : ℝ) + 2) (by linarith)
    have h2 : Real.sqrt ((n : ℝ) + 2) ≤ 2 * Real.sqrt n :=
      calc Real.sqrt ((n : ℝ) + 2) ≤ Real.sqrt ((2 * Real.sqrt n) ^ 2) :=
            Real.sqrt_le_sqrt (by nlinarith)
        _ = 2 * Real.sqrt n := Real.sqrt_sq (by positivity)
    linarith
  have he : nvεt n ^ 2 * Real.sqrt n ≤ 1 := by
    rw [nvεt_sq, one_div_mul_eq_div, div_le_one (Real.sqrt_pos.2 (by linarith))]
    exact Real.sqrt_le_sqrt (by linarith)
  have hs : (sRate n (nvJ n) (nva n) (nvεt n) : ℝ) ≤ n * nvεt n ^ 2 / Real.log ((n : ℝ) + 2) + 1 := by
    have hx : 0 ≤ n * nvεt n ^ 2 / Real.log ((n : ℝ) + 2) := by positivity
    unfold sRate nva
    rw [Nat.cast_max, hJ, Nat.cast_one]
    exact max_le (by linarith) (Nat.ceil_lt_add_one hx).le
  have h1 : (sRate n (nvJ n) (nva n) (nvεt n) : ℝ) * Real.log ((n : ℝ) + 2) ≤
      n * nvεt n ^ 2 + Real.log ((n : ℝ) + 2) := by
    calc (sRate n (nvJ n) (nva n) (nvεt n) : ℝ) * Real.log ((n : ℝ) + 2)
        ≤ (n * nvεt n ^ 2 / Real.log ((n : ℝ) + 2) + 1) * Real.log ((n : ℝ) + 2) :=
          mul_le_mul_of_nonneg_right hs hL.le
      _ = n * nvεt n ^ 2 + Real.log ((n : ℝ) + 2) := by field_simp
  rw [hJ, div_le_div_iff₀ hn0 hr]
  calc (sRate n (nvJ n) (nva n) (nvεt n) : ℝ) * Real.log ((n : ℝ) + 2) * Real.sqrt n
      ≤ (n * nvεt n ^ 2 + Real.log ((n : ℝ) + 2)) * Real.sqrt n :=
        mul_le_mul_of_nonneg_right h1 hr.le
    _ = n * (nvεt n ^ 2 * Real.sqrt n) + Real.log ((n : ℝ) + 2) * Real.sqrt n := by ring
    _ ≤ n * 1 + 4 * Real.sqrt n * Real.sqrt n :=
        add_le_add (mul_le_mul_of_nonneg_left he hn0.le)
          (mul_le_mul_of_nonneg_right hLle hr.le)
    _ = 5 * n := by linear_combination 4 * hr2

private lemma nv_hs :
    Tendsto (fun n : ℕ => (sRate n (nvJ n) (nva n) (nvεt n) : ℝ) * Real.log (nvJ n) / n)
      atTop (𝓝 0) := by
  have h5 : Tendsto (fun n : ℕ => 5 / Real.sqrt n) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (Real.tendsto_sqrt_atTop.comp tendsto_natCast_atTop_atTop)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h5
    (Filter.Eventually.of_forall fun n => ?_) (Filter.eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  · have : 0 ≤ Real.log (nvJ n) := Real.log_nonneg (by rw [nvJ_cast]; linarith [n.cast_nonneg (α := ℝ)])
    positivity
  · exact nv_hs_bound hn

/-- The coordinate `1` of `Fin (nvJ n)`. -/
private def nvOne (n : ℕ) : Fin (nvJ n) := ⟨1, by unfold nvJ; omega⟩

private lemma nv_sparse (n : ℕ) :
    ∃ θ₀ S, SparseApprox (nvX n) (nvf₀ n) (nvεt n) (nvδ n) (nvE n) (nva n) θ₀ S := by
  have hδ : 0 < nvδ n := div_pos (nvεt_pos n) (by rw [nvJ_cast]; positivity)
  refine ⟨Pi.single (nvOne n) 1, {nvOne n}, ?_, ?_, ?_, ?_, ?_⟩
  · have h0 : nvf₀ n - nvX n *ᵥ Pi.single (nvOne n) 1 = 0 := by
      funext i
      simp [nvf₀, nvX, designMatrix, fourierTensor, Matrix.mulVec_single, nvOne]
    rw [h0, empNorm_zero]
    exact (nvεt_pos n).le
  · unfold numLarge nva
    refine (card_le_card fun j hj => ?_).trans (card_singleton (nvOne n)).le
    simp only [mem_filter, mem_univ, true_and] at hj
    rw [mem_singleton]
    by_contra h
    rw [Pi.single_eq_of_ne h, abs_zero] at hj
    linarith
  · intro j
    unfold nvE
    by_cases h : j = nvOne n
    · subst h; simp
    · rw [Pi.single_eq_of_ne h, abs_zero]; exact zero_le_one
  · rfl
  · intro j hj
    rw [mem_singleton] at hj
    rw [Pi.single_eq_of_ne hj, abs_zero]
    exact hδ.le

private lemma nv_budget {n : ℕ} (hn : 2 ≤ n) :
    (nva n : ℝ) * Real.log (nvJ n) ≤ 4 * n * nvεt n ^ 2 ∧
    Real.log (1 / nvεt n) ≤ 4 * Real.log (nvJ n) ∧
    Real.log (1 / nvτ n) ≤ 4 * Real.log (nvJ n) ∧
    Real.log (nvE n) ≤ 4 * Real.log (nvJ n) := by
  have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hL0 : 0 ≤ Real.log ((n : ℝ) + 2) := Real.log_nonneg (by linarith)
  have hlog1 : Real.log ((n : ℝ) + 1) ≤ Real.log ((n : ℝ) + 2) :=
    Real.log_le_log (by linarith) (by linarith)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [nvJ_cast, nvεt_sq]
    simp only [nva, Nat.cast_one, one_mul]
    have hq : 0 < Real.sqrt ((n : ℝ) + 1) := Real.sqrt_pos.2 (by linarith)
    have hp : 0 < Real.sqrt ((n : ℝ) + 2) := Real.sqrt_pos.2 (by linarith)
    have hqp : Real.sqrt ((n : ℝ) + 1) ≤ Real.sqrt ((n : ℝ) + 2) := Real.sqrt_le_sqrt (by linarith)
    have hpp : Real.sqrt ((n : ℝ) + 2) * Real.sqrt ((n : ℝ) + 2) = (n : ℝ) + 2 :=
      Real.mul_self_sqrt (by linarith)
    have hlog := log_le_two_sqrt (x := (n : ℝ) + 2) (by linarith)
    rw [mul_one_div, le_div_iff₀ hq]
    have h1 := mul_le_mul_of_nonneg_right hlog hq.le
    have h2 := mul_le_mul_of_nonneg_left hqp hp.le
    nlinarith
  · rw [nvJ_cast, one_div (nvεt n), Real.log_inv]
    unfold nvεt
    rw [Real.log_rpow (by positivity)]
    have : 0 ≤ Real.log ((n : ℝ) + 1) := Real.log_nonneg (by linarith)
    linarith
  · unfold nvτ
    rw [ite_eq_right (by omega), nvJ_cast, one_div_div,
      Real.log_div (Real.sqrt_pos.2 (by linarith)).ne' (by positivity),
      Real.log_sqrt (by linarith), Real.log_rpow (by linarith)]
    have : Real.log (n : ℝ) ≤ Real.log ((n : ℝ) + 2) := Real.log_le_log (by linarith) (by linarith)
    linarith
  · unfold nvE
    rw [Real.log_one, nvJ_cast]
    linarith

/-- **Non-vacuity**: the concrete instance satisfies every hypothesis of Theorem 1 for the
horseshoe prior, with `σ = 1`, `K = √2`, `η = 1/2`, `μ'' = 1`, `c_δ = 1`, `c_τ = 1`, `B = 4`. -/
theorem nonvacuity :
    MainHorseshoeHyp nvJ nvX nvf₀ 1 nvτ nvεt nvδ nvE nvM nva (Real.sqrt 2 ^ 1) (1 / 2) 1 1 1 4 := by
  have hJpos : ∀ n, (0 : ℝ) < ((nvJ n : ℕ) : ℝ) := fun n => by rw [nvJ_cast]; positivity
  exact
  { hσ := one_pos
    hK := by positivity
    hη := by norm_num
    hη1 := by norm_num
    hμ'' := one_pos
    hcδ := one_pos
    hcτ := one_pos
    hB := by norm_num
    hJ := tendsto_add_atTop_nat 2
    hnεt := nv_hnεt
    hs := nv_hs
    hM := Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    hτ := Filter.eventually_atTop.2 ⟨1, fun n hn => by
      unfold nvτ
      rw [ite_eq_right (by omega)]
      exact div_pos (Real.rpow_pos_of_pos (hJpos n) _) (Real.sqrt_pos.2 (by exact_mod_cast hn))⟩
    hεt := Filter.Eventually.of_forall nvεt_pos
    hδ := Filter.Eventually.of_forall fun n => div_pos (nvεt_pos n) (hJpos n)
    hE := Filter.Eventually.of_forall fun _ => one_pos
    ha := Filter.Eventually.of_forall fun n => ⟨le_rfl, by unfold nva nvJ; omega⟩
    hδεt := Filter.Eventually.of_forall fun _ => le_rfl
    hbasis := Filter.Eventually.of_forall fun n =>
      fourier_basis n (nvJ n) 1 (fun j _ => (j : ℕ)) (fun i _ => (i : ℝ) / n)
    hA2 := Filter.Eventually.of_forall nv_sparse
    hcδev := Filter.Eventually.of_forall fun n => by rw [one_mul]; exact le_rfl
    hτev := Filter.eventually_atTop.2 ⟨1, fun n hn => by
      unfold nvτ
      rw [ite_eq_right (by omega)]
      norm_num⟩
    hbudget := Filter.eventually_atTop.2 ⟨2, fun n hn => nv_budget hn⟩ }

/-- The conclusion of Theorem 1 for the concrete instance. -/
theorem nonvacuity_conclusion :
    AsymptoticConclusion nvJ nvX nvf₀ 1 (fun n => horseshoePDF (nvτ n)) nvεt nvδ nvM nva
      (Real.sqrt 2 ^ 1) (1 / 2) (1 / 2) 1 (4 * (6 + 5 * 4)) :=
  main_horseshoe _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ nonvacuity

end LargePrior
