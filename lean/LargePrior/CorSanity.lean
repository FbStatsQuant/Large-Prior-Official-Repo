import LargePrior.Jackson

/-!
# Sanity lemmas for the corollary's definitions

Reductions to familiar cases and edge cases (including Lean conventions such as `x / 0 = 0`),
which would expose a wrongly written definition. Not restatements of the definitions.
-/

open Finset

noncomputable section

namespace LargePrior

/-- Isotropic smoothness: `α* = a`. -/
lemma alphaStar_iso {d : ℕ} (hd : 0 < d) (a : ℝ) : alphaStar (fun _ : Fin d => a) = a := by
  by_cases ha : a = 0
  · subst ha; simp [alphaStar]
  · have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
    simp only [alphaStar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp

/-- Isotropic budget exponent: `β_k = 1/(2a + d)`. -/
lemma betaExp_iso {d : ℕ} (hd : 0 < d) {a : ℝ} (ha : 0 < a) (k : Fin d) :
    betaExp (fun _ : Fin d => a) k = 1 / (2 * a + d) := by
  have h1 := alphaStar_iso hd a
  have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  unfold betaExp
  rw [h1]
  have : (2 * a + d) ≠ 0 := by positivity
  field_simp

/-- Univariate, `α = 1`: `r = D = β = 1/3`. -/
lemma exps_one : rateExp (fun _ : Fin 1 => (1 : ℝ)) = 1 / 3 ∧
    dimExp (fun _ : Fin 1 => (1 : ℝ)) = 1 / 3 ∧ betaExp (fun _ : Fin 1 => (1 : ℝ)) 0 = 1 / 3 := by
  have h1 : alphaStar (fun _ : Fin 1 => (1 : ℝ)) = 1 := alphaStar_iso (by norm_num) 1
  refine ⟨?_, ?_, ?_⟩
  · unfold rateExp; rw [h1]; norm_num
  · unfold dimExp; rw [h1]; norm_num
  · have := betaExp_iso (d := 1) (by norm_num) (a := 1) (by norm_num) 0
    rw [this]; norm_num

/-- Anisotropic `(α₁, α₂) = (1, 2)`: `α* = 4/3`, `r = 2/7`, `β = (2/7, 1/7)`. -/
lemma exps_aniso : alphaStar ![(1 : ℝ), 2] = 4 / 3 ∧ rateExp ![(1 : ℝ), 2] = 2 / 7 ∧
    betaExp ![(1 : ℝ), 2] 0 = 2 / 7 ∧ betaExp ![(1 : ℝ), 2] 1 = 1 / 7 := by
  have h1 : alphaStar ![(1 : ℝ), 2] = 4 / 3 := by
    simp only [alphaStar, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    norm_num
  refine ⟨h1, ?_, ?_, ?_⟩
  · unfold rateExp; rw [h1]; norm_num
  · unfold betaExp
    rw [h1]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_zero,
      zero_add, Nat.cast_ofNat, one_mul]
    norm_num
  · unfold betaExp
    rw [h1]
    simp only [Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, Matrix.cons_val_one,
      Matrix.cons_val_fin_one, zero_add, Nat.cast_ofNat, one_div]
    norm_num

/-- First forward differences are ordinary increments. -/
lemma fdiff_one (h : ℝ) (g : ℝ → ℝ) (x : ℝ) : fdiff 1 h g x = g (x + h) - g x := by
  simp only [fdiff, Nat.reduceAdd, sum_range_succ, range_one, sum_singleton, tsub_zero,
    pow_one, Nat.choose_succ_self_right, zero_add, Nat.cast_one, mul_one,
    CharP.cast_eq_zero, zero_mul, add_zero, neg_mul, one_mul, tsub_self, pow_zero, Nat.choose_self]
  ring

/-- Second forward differences have the usual three-term expansion. -/
lemma fdiff_two (h : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    fdiff 2 h g x = g x - 2 * g (x + h) + g (x + 2 * h) := by
  simp only [fdiff, Nat.reduceAdd, sum_range_succ, range_one, sum_singleton, tsub_zero,
    even_two, Even.neg_pow, one_pow, Nat.choose, Nat.cast_one, mul_one, CharP.cast_eq_zero,
    zero_mul, add_zero, one_mul, Nat.add_one_sub_one, pow_one, Nat.cast_ofNat, neg_mul,
    tsub_self, pow_zero, add_left_inj]
  ring

/-- A constant has vanishing differences of every order `r ≥ 1`. -/
lemma fdiff_const {r : ℕ} (hr : 1 ≤ r) (h c x : ℝ) : fdiff r h (fun _ => c) x = 0 := by
  have h1 : ∑ v ∈ range (r + 1), (-1 : ℝ) ^ (r - v) * (r.choose v : ℝ) = 0 := by
    have := (add_pow (1 : ℝ) (-1) r).symm
    rw [show (1 : ℝ) + -1 = 0 by norm_num, zero_pow (by omega)] at this
    simpa using this
  unfold fdiff
  calc ∑ v ∈ range (r + 1), (-1 : ℝ) ^ (r - v) * (r.choose v : ℝ) * c
      = (∑ v ∈ range (r + 1), (-1 : ℝ) ^ (r - v) * (r.choose v : ℝ)) * c := by
        rw [Finset.sum_mul]
    _ = 0 := by rw [h1, zero_mul]

/-- Evaluating a coordinate section at the original coordinate recovers the function. -/
lemma sectionAt_self {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (k : Fin d) :
    sectionAt f x k (x k) = f x := by
  simp [sectionAt]

/-- A constant `c` lies in every Hölder–Zygmund ball of radius `|c|` (with `r ≥ 1`). -/
lemma hzBall_const {d : ℕ} (α : Fin d → ℝ) {r : Fin d → ℕ} (hr : ∀ k, 1 ≤ r k) (c : ℝ) :
    HZBall α r |c| (fun _ => c) := by
  refine ⟨continuous_const, fun _ _ => rfl, |c|, 0, abs_nonneg c, le_refl _, by simp, fun _ => le_rfl, ?_⟩
  intro k x h _ _
  have : sectionAt (fun _ : Fin d → ℝ => c) x k = fun _ => c := rfl
  rw [this, fdiff_const (hr k) h c (x k)]
  simp

/-- The one-dimensional Hölder–Zygmund radius bounds the function pointwise. -/
lemma hzBall1_sup {α : ℝ} {r : ℕ} {R : ℝ} {g : ℝ → ℝ} (h : HZBall1 α r R g) (x : ℝ) :
    |g x| ≤ R := by
  obtain ⟨_, _, A, B, hA, hB, hAB, hg, _⟩ := h
  calc |g x| ≤ A := hg x
    _ ≤ A + B := by linarith
    _ ≤ R := hAB

/-- The first sine atom is a trigonometric polynomial of degree one. -/
lemma isTrigPoly_atom : IsTrigPoly 1 (fourierAtom 2) := by
  refine ⟨fun ν => if ν = 2 then 1 else 0, fun x => ?_⟩
  simp

/-- The degree-zero Fejér kernel is the constant one. -/
lemma fejerKernel_zero (u : ℝ) : fejerKernel 0 u = 1 := by
  simp [fejerKernel]

/-- The first Fourier indices have frequencies zero, one, one, and two. -/
lemma freq_examples : freq 0 = 0 ∧ freq 1 = 1 ∧ freq 2 = 1 ∧ freq 3 = 2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

/-- Small budgets select the expected dyadic atom counts and degrees. -/
lemma budget_examples : budgetAtoms 1 = 1 ∧ budgetAtoms 2 = 1 ∧ budgetAtoms 3 = 3 ∧
    budgetAtoms 6 = 3 ∧ budgetAtoms 7 = 7 ∧ budgetDeg 7 = 2 := by
  unfold budgetAtoms budgetDeg
  decide

/-- Small de la Vallée Poussin multipliers have the expected cutoff values. -/
lemma qMult_examples : qMult 2 0 = 1 ∧ qMult 2 1 = 0 ∧ qMult 3 1 = 1 ∧ qMult 3 2 = 0 ∧
    qMult 7 3 = 1 / 2 := by
  simp only [qMult, vdpMult, budgetDeg]
  norm_num

/-- For budgets `m ≤ 2`, `Q_m` returns the mean. -/
lemma Qop_one (g : ℝ → ℝ) (x : ℝ) : Qop 1 g x = ∫ t in (0 : ℝ)..1, g t := by
  simp [Qop, budgetAtoms, qMult, freq, coef, fourierAtom]

/-- Small spline orders and levels have the expected dimensions. -/
lemma splineDim_examples : splineDim 1 0 = 1 ∧ splineDim 2 1 = 3 ∧ splineDim 4 3 = 11 := by
  unfold splineDim
  decide

/-- The multilevel spline dimension sums the dimensions of its blocks. -/
lemma splineUnionDim_examples : splineUnionDim 1 1 = 3 ∧ splineUnionDim 2 2 = 10 := by
  unfold splineUnionDim splineDim
  decide

/-- Spline levels respect both the coefficient budget and the level cap. -/
lemma splineLevel_examples :
    splineLevel 1 3 5 = 2 ∧ splineLevel 4 3 2 = 0 ∧ splineLevel 1 2 100 = 2 := by
  unfold splineLevel splineDim
  decide

/-- Two nonzero entries give support cardinality two. -/
lemma suppCard_example : suppCard (![0, 2, 0, -1] : Fin 4 → ℝ) = 2 := by
  have : (univ.filter fun j : Fin 4 => (![0, 2, 0, -1] : Fin 4 → ℝ) j ≠ 0) = {1, 3} := by
    ext j
    fin_cases j <;> simp
  unfold suppCard
  rw [this]
  rfl

/-- With unit budget exponent, the univariate Fourier cutoff equals the sample size. -/
lemma fourierM_one (n : ℕ) : fourierM (fun _ : Fin 1 => (1 : ℝ)) n 0 = n := by
  simp [fourierM]

/-- The univariate Fourier dictionary then contains `2n + 1` atoms. -/
lemma fourierJ_one (n : ℕ) : fourierJ (fun _ : Fin 1 => (1 : ℝ)) n = 2 * n + 1 := by
  have h := fourierM_one n
  simp only [fourierJ, FourierIdx, Fintype.card_pi, Fintype.card_fin, Finset.univ_unique,
    Fin.default_eq_zero, Finset.prod_singleton, h]

/-- A sample size of eight gives dyadic spline level three. -/
lemma splineH_example : splineH (fun _ : Fin 1 => (1 : ℝ)) 8 0 = 3 := by
  have h8 : Real.logb 2 (8 : ℝ) = 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  unfold splineH
  simp only [Nat.cast_ofNat, h8]
  norm_num

/-- `J_n = ∏_k U_{H_{n,k}}` for the spline dictionary (here `q = 1`, `d = 1`, `n = 4`: `H = 2`,
`U_2 = 1 + 2 + 4 = 7`). -/
lemma splineJ_example : splineJ 1 (fun _ : Fin 1 => (1 : ℝ)) 4 = 7 := by
  have h4 : Real.logb 2 (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℝ) by norm_num, Real.logb_rpow (by norm_num) (by norm_num)]
  have hH : splineH (fun _ : Fin 1 => (1 : ℝ)) 4 0 = 2 := by
    unfold splineH
    simp only [Nat.cast_ofNat, h4]
    norm_num
  unfold splineJ
  simp only [SplineIdx, Fintype.card_pi, Fintype.card_sigma, Fintype.card_fin, Finset.univ_unique,
    Finset.prod_singleton]
  have hH' : splineH (fun _ : Fin 1 => (1 : ℝ)) 4 default = 2 := hH
  rw [Fin.sum_univ_eq_sum_range (fun ℓ => splineDim 1 ℓ), hH']
  decide

/-- Lean convention: with `J ≤ 1`, `log J = 0` and `N = n / 0 = 0`. -/
lemma corN_degenerate (n : ℕ) : corN n 1 = 0 := by
  simp [corN]

/-- The horseshoe scale is `1/16` for this concrete sample and dictionary size. -/
lemma corTau_example : corTau 1 4 2 = 1 / 16 := by
  unfold corTau
  have h1 : Real.sqrt ((4 : ℕ) : ℝ) = 2 := by
    rw [show ((4 : ℕ) : ℝ) = 2 ^ 2 by norm_num]
    exact Real.sqrt_sq (by norm_num)
  have h2 : ((2 : ℕ) : ℝ) ^ (-(2 + (1 : ℝ))) = 1 / 8 := by
    rw [show -(2 + (1 : ℝ)) = -((3 : ℕ) : ℝ) by norm_num, Real.rpow_neg (by norm_num),
      Real.rpow_natCast]
    norm_num
  rw [h1, h2]
  norm_num

/-- The unit cube contains its center. -/
lemma unitCube_center (d : ℕ) : (fun _ : Fin d => (1 / 2 : ℝ)) ∈ unitCube d := by
  intro k
  constructor <;> norm_num

end LargePrior
