import LargePrior.CorNonVacuity

/-!
# Non-vacuity, spline side, and Corollary 1 for univariate Hölder classes

For order `q = 1`: B-spline stability (`BSplineReadout 1 1`) and the one-block approximation of
every `α`-Hölder function on `[0,1]`, `0 < α ≤ 1`, are proved. Hence `cor_holder`: Corollary 1 for
the whole `C^α([0,1])` ball, `0 < α ≤ 1`, with no assumed classical input.
-/

open MeasureTheory Filter Finset
open scoped Topology Matrix

noncomputable section

namespace LargePrior

/-- For order 1, `knot 1 K i = i / K` when `i ≤ K`. -/
private lemma knot_one_eq {K i : ℕ} (hK : 0 < K) (hi : i ≤ K) : knot 1 K i = (i : ℝ) / K := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have h0 : 0 ≤ (i : ℝ) / K := by positivity
  have h1 : (i : ℝ) / K ≤ 1 := by
    rw [div_le_one hKR]; exact_mod_cast hi
  unfold knot
  simp only [Nat.cast_one, sub_self, sub_zero]
  rw [min_eq_right h1, max_eq_right h0]

/-- Support of the order-1 B-spline: `B_i(x) ≠ 0` forces `i/K ≤ x ≤ (i+1)/K`. -/
private lemma bspl_one_support {K i : ℕ} (hK : 0 < K) (hi : i < K) {x : ℝ}
    (h : bspl 1 K 1 i x ≠ 0) : (i : ℝ) / K ≤ x ∧ x ≤ ((i : ℝ) + 1) / K := by
  have hs := bspl_support (q := 1) (K := K) (k := 1) le_rfl h
  rw [knot_one_eq hK hi.le, knot_one_eq hK (by omega)] at hs
  push_cast at hs
  exact hs

/-- A one-block spline in dimension one with coefficients depending on `j 0` only. -/
private lemma blockSeries_one_eq (ℓ : Fin 1 → ℕ) (g : ℕ → ℝ) (x : Fin 1 → ℝ) :
    blockSeries 1 ℓ (fun j => g (j 0 : ℕ)) x =
      ∑ i ∈ range (2 ^ ℓ 0 + 1 - 1), g i * bspl 1 (2 ^ ℓ 0) 1 i (x 0) := by
  unfold blockSeries
  simp only [Fin.prod_univ_one]
  rw [← Fin.sum_univ_eq_sum_range (fun i => g i * bspl 1 (2 ^ ℓ 0) 1 i (x 0))]
  exact Fintype.sum_equiv (Equiv.piUnique _) _ _ (fun j => rfl)

/-- `β = 1/(2α + 1)` in dimension one (helper, used before `betaExp_dim_one` is declared). -/
private lemma betaExp_dim_one_aux {α : ℝ} (hα : 0 < α) (k : Fin 1) :
    betaExp (fun _ : Fin 1 => α) k = 1 / (2 * α + 1) := by
  have hα' : α ≠ 0 := hα.ne'
  have h2 : 2 * α + 1 ≠ 0 := by positivity
  unfold betaExp alphaStar
  simp only [Fin.sum_univ_one, Nat.cast_one, one_div, inv_inv]
  field_simp

/-- Order-1 Hölder approximation error at a point, at level `L`. -/
private lemma holder_err {α R : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hf : HolderBall1 α R f) (L : ℕ)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1) :
    |f t - ∑ i ∈ range (2 ^ L + 1 - 1), f ((i : ℝ) / ((2 ^ L : ℕ) : ℝ)) * bspl 1 (2 ^ L) 1 i t| ≤
      R * ((2 ^ L : ℕ) : ℝ) ^ (-α) := by
  have hK : 0 < 2 ^ L := by positivity
  have hKR : (0 : ℝ) < ((2 ^ L : ℕ) : ℝ) := by exact_mod_cast hK
  have hR : 0 ≤ R := le_trans (abs_nonneg _) (hf.1 0 ⟨le_rfl, zero_le_one⟩)
  have hpu := bspl_sum_eq_one (q := 1) (K := 2 ^ L) (k := 1) le_rfl Nat.one_le_two_pow le_rfl le_rfl ht
  set E : ℝ := ((2 ^ L : ℕ) : ℝ) ^ (-α) with hE
  have hsplit : f t - ∑ i ∈ range (2 ^ L + 1 - 1),
      f ((i : ℝ) / ((2 ^ L : ℕ) : ℝ)) * bspl 1 (2 ^ L) 1 i t =
      ∑ i ∈ range (2 ^ L + 1 - 1),
        (f t - f ((i : ℝ) / ((2 ^ L : ℕ) : ℝ))) * bspl 1 (2 ^ L) 1 i t := by
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hpu, mul_one]
  have hterm : ∀ i ∈ range (2 ^ L + 1 - 1),
      |(f t - f ((i : ℝ) / ((2 ^ L : ℕ) : ℝ))) * bspl 1 (2 ^ L) 1 i t| ≤
        R * E * bspl 1 (2 ^ L) 1 i t := by
    intro i hi
    have hi' : i < 2 ^ L := by rw [Finset.mem_range] at hi; omega
    have hB := bspl_nonneg 1 (2 ^ L) 1 i t
    rw [abs_mul, abs_of_nonneg hB]
    by_cases h0 : bspl 1 (2 ^ L) 1 i t = 0
    · rw [h0, mul_zero, mul_zero]
    refine mul_le_mul_of_nonneg_right ?_ hB
    obtain ⟨ha, hb⟩ := bspl_one_support hK hi' h0
    have hiR : ((i : ℕ) : ℝ) + 1 ≤ ((2 ^ L : ℕ) : ℝ) := by exact_mod_cast hi'
    have hmem : (i : ℝ) / ((2 ^ L : ℕ) : ℝ) ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by positivity, by rw [div_le_one hKR]; linarith⟩
    have hdist : |t - (i : ℝ) / ((2 ^ L : ℕ) : ℝ)| ≤ (((2 ^ L : ℕ) : ℝ))⁻¹ := by
      rw [abs_of_nonneg (by linarith)]
      have : ((i : ℝ) + 1) / ((2 ^ L : ℕ) : ℝ) =
          (i : ℝ) / ((2 ^ L : ℕ) : ℝ) + (((2 ^ L : ℕ) : ℝ))⁻¹ := by
        rw [add_div, one_div]
      linarith
    calc |f t - f ((i : ℝ) / ((2 ^ L : ℕ) : ℝ))|
        ≤ R * |t - (i : ℝ) / ((2 ^ L : ℕ) : ℝ)| ^ α := hf.2 t ht _ hmem
      _ ≤ R * ((((2 ^ L : ℕ) : ℝ))⁻¹) ^ α :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (abs_nonneg _) hdist hα.le) hR
      _ = R * E := by rw [hE, Real.rpow_neg hKR.le, Real.inv_rpow hKR.le]
  rw [hsplit]
  calc _ ≤ ∑ i ∈ range (2 ^ L + 1 - 1),
        |(f t - f ((i : ℝ) / ((2 ^ L : ℕ) : ℝ))) * bspl 1 (2 ^ L) 1 i t| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ range (2 ^ L + 1 - 1), R * E * bspl 1 (2 ^ L) 1 i t := Finset.sum_le_sum hterm
    _ = R * E := by rw [← Finset.mul_sum, hpu, mul_one]

/-- **Classical spline stability for order 1** (`C_dual = 1`): proved, not assumed. -/
theorem bsplineReadout_one : BSplineReadout 1 1 := by
  intro ℓ θ S hS j
  have hK : 0 < 2 ^ ℓ := by positivity
  have hKR : (0 : ℝ) < ((2 ^ ℓ : ℕ) : ℝ) := by exact_mod_cast hK
  have hD : splineDim 1 ℓ = 2 ^ ℓ := by simp [splineDim]
  have hj : (j : ℕ) < 2 ^ ℓ := hD ▸ j.isLt
  have hjR : ((j : ℕ) : ℝ) + 1 ≤ ((2 ^ ℓ : ℕ) : ℝ) := by exact_mod_cast hj
  set x : ℝ := (((j : ℕ) : ℝ) + 1 / 2) / ((2 ^ ℓ : ℕ) : ℝ) with hx
  have hx01 : x ∈ Set.Icc (0 : ℝ) 1 := by
    refine ⟨by positivity, ?_⟩
    rw [hx, div_le_one hKR]; linarith
  have hsum : ∑ i, θ i * bspline 1 (2 ^ ℓ) (i : ℕ) x = θ j := by
    rw [Finset.sum_eq_single j]
    · have h1 : bspline 1 (2 ^ ℓ) (j : ℕ) x = 1 := by
        unfold bspline
        show (if _ then _ else _) = _
        refine ite_eq_left (Or.inl ⟨?_, ?_⟩)
        · rw [knot_one_eq hK hj.le, hx, div_le_div_iff_of_pos_right hKR]; linarith
        · rw [knot_one_eq hK (by omega), hx, div_lt_div_iff_of_pos_right hKR]; push_cast; linarith
      rw [h1, mul_one]
    · intro i _ hij
      have hi : (i : ℕ) < 2 ^ ℓ := hD ▸ i.isLt
      have h0 : bspline 1 (2 ^ ℓ) (i : ℕ) x = 0 := by
        by_contra hne
        obtain ⟨ha, hb⟩ := bspl_one_support hK hi hne
        rw [hx, div_le_div_iff_of_pos_right hKR] at ha hb
        have h1 : (i : ℕ) < (j : ℕ) + 1 := by
          have : ((i : ℕ) : ℝ) < ((j : ℕ) : ℝ) + 1 := by linarith
          exact_mod_cast this
        have h2 : (j : ℕ) < (i : ℕ) + 1 := by
          have : ((j : ℕ) : ℝ) < ((i : ℕ) : ℝ) + 1 := by linarith
          exact_mod_cast this
        exact hij (Fin.ext (by omega))
      rw [h0, mul_zero]
    · intro h; exact absurd (Finset.mem_univ j) h
  have := hS x hx01
  rw [hsum] at this
  linarith

/-- **One-block approximation of the constant `1`** (exact, partition of unity), order 1. -/
theorem splineOneBlock_one : SplineOneBlock (d := 1) 1 (fun _ => 1) 0 (fun _ => 1) := by
  intro ℓ
  refine ⟨fun _ => 1, fun x hx => ?_⟩
  have h := blockSeries_one_eq ℓ (fun _ => 1) x
  simp only [one_mul] at h
  have hK : 1 ≤ 2 ^ ℓ 0 := Nat.one_le_two_pow
  rw [h, bspl_sum_eq_one le_rfl hK le_rfl le_rfl (hx 0)]
  simp

/-- **Non-vacuity of `CorBSplineHyp`**: order `q = 1`, `f₀ = 1`, `R = 1`, design in `[0,1]`. -/
theorem corBSpline_nonvacuity :
    CorBSplineHyp (d := 1) 1 (fun _ => 1) (fun _ => 1) 1 (fun _ => 1) nvDesign 1 (1 / 2) 1 := by
  refine ⟨one_pos, le_rfl, fun _ => one_pos, fun k => ?_, fun _ _ => by simp, nvDesign_mem,
    one_pos, by norm_num, by norm_num, one_pos⟩
  rw [betaExp_dim_one_aux one_pos k]
  norm_num

/-- The B-spline end-to-end corollary applies to the `q = 1`, `f₀ = 1` instance with every
hypothesis proved, including the classical inputs. -/
theorem corBSpline_instance_conclusion : ∃ Csp Ceps c5 : ℝ, 0 < Csp ∧ 0 < Ceps ∧ 0 ≤ c5 ∧
    CorConclusion (d := 1) (fun _ => 1) (splineJ 1 fun _ => 1) (splineX 1 (fun _ => 1) nvDesign)
      (fun n i => (fun _ : Fin 1 → ℝ => (1 : ℝ)) (nvDesign n i)) 1
      (fun n => horseshoePDF (corTau 1 n (splineJ 1 (fun _ : Fin 1 => (1 : ℝ)) n))) Csp Ceps
      (1 / 2) (Aconst 1 (1 / 2) 1 (1 / 2) 1 c5) := by
  obtain ⟨Csp, Ceps, E, h1, h2, -, H⟩ := cor_bspline 1 1 (fun _ => 1) 0 1 1 le_rfl
    (fun _ => one_pos) le_rfl le_rfl bsplineReadout_one
  obtain ⟨c5, hc5, -, hconc⟩ := H (fun _ => 1) (fun _ => 1) nvDesign 1 (1 / 2) 1 (1 / 2)
    splineOneBlock_one corBSpline_nonvacuity (by norm_num) (by norm_num)
  exact ⟨Csp, Ceps, c5, h1, h2, hc5, hconc⟩

/-- `β = 1/(2α + 1)` in dimension one. -/
lemma betaExp_dim_one {α : ℝ} (hα : 0 < α) (k : Fin 1) :
    betaExp (fun _ : Fin 1 => α) k = 1 / (2 * α + 1) := by
  exact betaExp_dim_one_aux hα k

/-- **One-block approximation of `α`-Hölder functions by order-1 splines**, `0 < α ≤ 1`:
`θ_i = f(i/2^ℓ)` gives error at most `R 2^{−ℓα} = R D_ℓ^{−α}` on `[0,1]` (proved, not assumed). -/
theorem splineOneBlock_holder {α R : ℝ} {f : ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hf : HolderBall1 α R f) : SplineOneBlock (d := 1) 1 (fun _ => α) R (fun y => f (y 0)) := by
  -- The statement retains `hα1`; this approximation proof only needs `hα > 0`.
  have _ := hα1
  intro ℓ
  refine ⟨fun j => (fun i : ℕ => f ((i : ℝ) / ((2 ^ ℓ 0 : ℕ) : ℝ))) (j 0 : ℕ), fun x hx => ?_⟩
  rw [blockSeries_one_eq ℓ (fun i : ℕ => f ((i : ℝ) / ((2 ^ ℓ 0 : ℕ) : ℝ))) x, Fin.sum_univ_one]
  beta_reduce
  exact holder_err hα hf (ℓ 0) (hx 0)

/-- **Corollary 1 for univariate `α`-Hölder classes, `0 < α ≤ 1`, with no assumed input.** -/
theorem cor_holder : CorHolderStatement := by
  intro α R hα hα1 hR
  obtain ⟨Csp, Ceps, E, hCsp, hCeps, hE, H⟩ := cor_bspline 1 1 (fun _ => α) R 1 R le_rfl
    (fun _ => hα) hR le_rfl bsplineReadout_one
  refine ⟨Csp, Ceps, E, hCsp, hCeps, hE, ?_⟩
  intro b f₀ x σ η μ'' cδ hf hb hx hσ hη hη1 hμ'' hcδ hcδ1
  exact H (fun _ => b) (fun y => f₀ (y 0)) x σ η μ'' cδ (splineOneBlock_holder hα hα1 hf)
    { hd := one_pos, hq := le_rfl, hα := fun _ => hα
      hb := fun k => by rw [betaExp_dim_one hα k]; exact hb
      hf₀ := fun y hy => hf.1 (y 0) (hy 0), hx := hx, hσ := hσ, hη := hη, hη1 := hη1
      hμ'' := hμ'' } hcδ hcδ1

/-- `x ↦ x` lies in the Lipschitz ball of radius 1 on `[0,1]`. -/
lemma holderBall1_id : HolderBall1 1 1 id := by
  refine ⟨fun x hx => ?_, fun x _ y _ => ?_⟩
  · rw [id, abs_of_nonneg hx.1]; exact hx.2
  · simp [Real.rpow_one]

/-- Instance: Corollary 1 for `f₀(x) = x` (outside every finite order-1 spline span, so positive
uniform approximation error on `[0,1]`; with `b = 1` the empirical error at the design can be zero),
`x_i = i/n`, order-1 splines with `b = 1`, horseshoe prior: rate `(n/log n)^{−1/3}`. -/
theorem corHolder_id_conclusion : ∃ Csp Ceps c5 : ℝ, 0 < Csp ∧ 0 < Ceps ∧ 0 ≤ c5 ∧
    CorConclusion (fun _ : Fin 1 => (1 : ℝ)) (splineJ 1 fun _ : Fin 1 => (1 : ℝ))
      (splineX 1 (fun _ : Fin 1 => (1 : ℝ)) nvDesign) (fun n i => id (nvDesign n i 0)) 1
      (fun n => horseshoePDF (corTau 1 n (splineJ 1 (fun _ : Fin 1 => (1 : ℝ)) n))) Csp Ceps
      (1 / 2) (Aconst 1 (1 / 2) 1 (1 / 2) 1 c5) := by
  obtain ⟨Csp, Ceps, E, h1, h2, -, H⟩ := cor_holder 1 1 one_pos le_rfl zero_le_one
  obtain ⟨c5, hc5, -, hconc⟩ := H 1 id nvDesign 1 (1 / 2) 1 (1 / 2) holderBall1_id
    (by norm_num) nvDesign_mem one_pos (by norm_num) (by norm_num) one_pos (by norm_num)
    (by norm_num)
  exact ⟨Csp, Ceps, c5, h1, h2, hc5, hconc⟩

end LargePrior
