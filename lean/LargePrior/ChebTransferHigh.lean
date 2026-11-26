import LargePrior.ChebTransfer

/-!
# LargePrior: the smoothness transfer for the Chebyshev fold, general `α` (L-02, Lane A)

`cheb_transfer`: for `0 < α < r`, `f ∈ C^α([0,1])` with radius `R` gives `f ∘ x` in the periodic
Hölder–Zygmund ball of radius `C_tr(α) R` (eq:cheb-transfer, D:538–554).

* T2: `iteratedDeriv_fwdDiff_tr` (differences commute with derivatives) and
  `abs_fwdDiff_iter_le_of_iteratedDeriv` (`|Δ_h^m ψ| ≤ |h|^m sup|ψ^{(m)}|`).
* T3: the representation `(f ∘ x)^{(t)} = Σ_k f^{(k)}(x) W_{t,k}` with within-derivatives on
  `[0,1]`, the Bell recurrence for `W_{t,k}` and the bound
  `|W_{t,k}^{(j)}| ≤ 2^{-k} (2π)^{t+j} k^j S(t,k)` (route of spike S2).
* T4: the Hölder bound of `(f ∘ x)^{(s)}` and the assembly.

Departures from the paper (PLAN §9.7). The paper extends `f₀` by Taylor polynomials (D:538) and
uses the set-partition form of Faà di Bruno (D:540–544): here the chain rule is applied with
derivatives within `[0,1]` (the fold maps into `[0,1]`), and the `W_{t,k}` are defined by the
recurrence `W_{t+1,k} = W_{t,k}' + x' W_{t,k-1}`, whose bound gives the same `A_k`. The s-fold
integral (D:550) is replaced by `s` applications of the mean value theorem.
-/

open Real
open scoped ContDiff

noncomputable section

namespace LargePrior

/-! ## Fold derivatives (spike S2) -/

private theorem hasDerivAt_chebFold (u : ℝ) :
    HasDerivAt chebFold (-(π * Real.sin (2 * π * u))) u := by
  have h := (((hasDerivAt_id' u).const_mul (2 * π)).cos.const_add 1).div_const 2
  show HasDerivAt (fun v => (1 + Real.cos (2 * π * v)) / 2) _ u
  convert h using 1
  ring

private theorem deriv_chebFold : deriv chebFold = fun u => -(π * Real.sin (2 * π * u)) :=
  funext fun u => (hasDerivAt_chebFold u).deriv

private theorem hasDerivAt_mul_cos (c a φ u : ℝ) :
    HasDerivAt (fun v => c * Real.cos (a * v + φ)) (c * a * Real.cos (a * u + φ + π / 2)) u := by
  have h : HasDerivAt (fun v => c * Real.cos (a * v + φ))
      (c * (-Real.sin (a * u + φ) * (a * 1))) u :=
    (((hasDerivAt_id' u).const_mul a).add_const φ).cos.const_mul c
  convert h using 1
  rw [Real.cos_add_pi_div_two]
  ring

/-- `x^{(j+1)}(u) = ½ (2π)^{j+1} cos(2πu + (j+1)π/2)` (D:494–496; positive orders only, the
order-zero value keeps the constant `½`). -/
private theorem iteratedDeriv_succ_chebFold (j : ℕ) :
    iteratedDeriv (j + 1) chebFold =
      fun u => (2 * π) ^ (j + 1) / 2 * Real.cos (2 * π * u + ((j : ℝ) + 1) * (π / 2)) := by
  induction j with
  | zero =>
    rw [zero_add, iteratedDeriv_one, deriv_chebFold]
    funext u
    simp only [Nat.cast_zero, zero_add, one_mul, pow_one]
    rw [Real.cos_add_pi_div_two]
    ring
  | succ n ih =>
    rw [iteratedDeriv_succ, ih]
    funext u
    rw [(hasDerivAt_mul_cos ((2 * π) ^ (n + 1) / 2) (2 * π) (((n : ℝ) + 1) * (π / 2)) u).deriv,
      show 2 * π * u + ((n : ℝ) + 1) * (π / 2) + π / 2 =
        2 * π * u + (((n + 1 : ℕ) : ℝ) + 1) * (π / 2) by push_cast; ring]
    ring

/-- `|x^{(i+1)}(u)| ≤ ½ (2π)^{i+1}` (eq:cheb-fold-bounds). -/
private theorem abs_iteratedDeriv_succ_chebFold_le (i : ℕ) (u : ℝ) :
    |iteratedDeriv (i + 1) chebFold u| ≤ (2 * π) ^ (i + 1) / 2 := by
  rw [iteratedDeriv_succ_chebFold, abs_mul, abs_of_pos (by positivity)]
  exact mul_le_of_le_one_right (by positivity) (Real.abs_cos_le_one _)

/-- Chain-rule step: `(F ∘ x · W)' = F'(x) x' W + F(x) W'`, with `F` differentiable within
`[0,1]` at `x(u)` only. -/
private theorem hasDerivAt_comp_chebFold_mul {F W : ℝ → ℝ} {F' W' u : ℝ}
    (hF : HasDerivWithinAt F F' (Set.Icc 0 1) (chebFold u)) (hW : HasDerivAt W W' u) :
    HasDerivAt (fun v => F (chebFold v) * W v)
      (F' * deriv chebFold u * W u + F (chebFold u) * W') u := by
  have hx := hasDerivAt_chebFold u
  have h1 : HasDerivAt (F ∘ chebFold) ((-(π * Real.sin (2 * π * u))) • F') u :=
    hF.scomp_hasDerivAt u hx chebFold_mem_Icc_tr
  rw [hx.deriv]
  exact (h1.mul hW).congr_deriv (by simp only [smul_eq_mul, Function.comp_apply]; ring)

private theorem contDiffAt_of_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) (n : ℕ) (u : ℝ) :
    ContDiffAt ℝ n f u :=
  (contDiff_infty.mp hf n).contDiffAt

private theorem differentiable_of_smooth {f : ℝ → ℝ} (hf : ContDiff ℝ ∞ f) :
    Differentiable ℝ f :=
  (contDiff_infty.mp hf 1).differentiable (by simp)

/-! ## The Bell-recurrence bound (spike S2) -/

/-- Bell step for one `k = m + 1`: `A = W_{s,m+1}` and `B = W_{s,m}` bounded at order `s` give
`A' + x' B = W_{s+1,m+1}` bounded at order `s + 1`. -/
private theorem bell_step {x A B : ℝ → ℝ} (hx : ContDiff ℝ ∞ x) (hA : ContDiff ℝ ∞ A)
    (hB : ContDiff ℝ ∞ B)
    (hxb : ∀ (i : ℕ) (u : ℝ), |iteratedDeriv (i + 1) x u| ≤ (2 * π) ^ (i + 1) / 2) (s m : ℕ)
    (hAb : ∀ (j : ℕ) (u : ℝ), |iteratedDeriv j A u| ≤
      ((2 : ℝ) ^ (m + 1))⁻¹ * (2 * π) ^ (s + j) * ((m + 1 : ℕ) : ℝ) ^ j *
        (Nat.stirlingSecond s (m + 1) : ℝ))
    (hBb : ∀ (j : ℕ) (u : ℝ), |iteratedDeriv j B u| ≤
      ((2 : ℝ) ^ m)⁻¹ * (2 * π) ^ (s + j) * (m : ℝ) ^ j * (Nat.stirlingSecond s m : ℝ))
    (j : ℕ) (u : ℝ) :
    |iteratedDeriv j (fun v => deriv A v + deriv x v * B v) u| ≤
      ((2 : ℝ) ^ (m + 1))⁻¹ * (2 * π) ^ (s + 1 + j) * ((m + 1 : ℕ) : ℝ) ^ j *
        (Nat.stirlingSecond (s + 1) (m + 1) : ℝ) := by
  have hA' : ContDiff ℝ ∞ (deriv A) := (contDiff_infty_iff_deriv.mp hA).2
  have hx' : ContDiff ℝ ∞ (deriv x) := (contDiff_infty_iff_deriv.mp hx).2
  rw [iteratedDeriv_fun_add (contDiffAt_of_smooth hA' j u)
      (contDiffAt_of_smooth (hx'.mul hB) j u),
    iteratedDeriv_fun_mul (contDiffAt_of_smooth hx' j u) (contDiffAt_of_smooth hB j u)]
  simp only [← iteratedDeriv_succ']
  have hsum : ∑ i ∈ Finset.range (j + 1),
      |(j.choose i : ℝ) * iteratedDeriv (i + 1) x u * iteratedDeriv (j - i) B u| ≤
      ((2 : ℝ) ^ (m + 1))⁻¹ * (2 * π) ^ (s + 1 + j) * (Nat.stirlingSecond s m : ℝ) *
        (1 + (m : ℝ)) ^ j := by
    rw [add_pow, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    have hij : i ≤ j := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    rw [abs_mul, abs_mul, Nat.abs_cast]
    calc (j.choose i : ℝ) * |iteratedDeriv (i + 1) x u| * |iteratedDeriv (j - i) B u|
        ≤ (j.choose i : ℝ) * ((2 * π) ^ (i + 1) / 2) *
            (((2 : ℝ) ^ m)⁻¹ * (2 * π) ^ (s + (j - i)) * (m : ℝ) ^ (j - i) *
              (Nat.stirlingSecond s m : ℝ)) := by
          gcongr
          · exact hxb i u
          · exact hBb (j - i) u
      _ = _ := by
          rw [show (2 * π) ^ (s + 1 + j) = (2 * π) ^ (i + 1) * (2 * π) ^ (s + (j - i)) by
            rw [← pow_add]; congr 1; omega]
          simp only [one_pow, one_mul]
          ring
  calc _ ≤ |iteratedDeriv (j + 1) A u| + ∑ i ∈ Finset.range (j + 1),
          |(j.choose i : ℝ) * iteratedDeriv (i + 1) x u * iteratedDeriv (j - i) B u| :=
        (abs_add_le _ _).trans (by gcongr; exact Finset.abs_sum_le_sum_abs _ _)
    _ ≤ ((2 : ℝ) ^ (m + 1))⁻¹ * (2 * π) ^ (s + (j + 1)) * ((m + 1 : ℕ) : ℝ) ^ (j + 1) *
          (Nat.stirlingSecond s (m + 1) : ℝ) +
        ((2 : ℝ) ^ (m + 1))⁻¹ * (2 * π) ^ (s + 1 + j) * (Nat.stirlingSecond s m : ℝ) *
          (1 + (m : ℝ)) ^ j := add_le_add (hAb (j + 1) u) hsum
    _ = _ := by
        rw [Nat.stirlingSecond_succ_succ]
        push_cast
        ring

/-- `|W_{s,k}^{(j)}| ≤ 2^{-k} (2π)^{s+j} k^j S(s,k)` for all `j, k` (with `0^0 = 1`). -/
private def BellBound (W : ℕ → ℕ → ℝ → ℝ) (s : ℕ) : Prop :=
  ∀ (k j : ℕ) (u : ℝ), |iteratedDeriv j (W s k) u| ≤
    ((2 : ℝ) ^ k)⁻¹ * (2 * π) ^ (s + j) * (k : ℝ) ^ j * (Nat.stirlingSecond s k : ℝ)

private theorem bellBound_succ {x : ℝ → ℝ} (hx : ContDiff ℝ ∞ x)
    (hxb : ∀ (i : ℕ) (u : ℝ), |iteratedDeriv (i + 1) x u| ≤ (2 * π) ^ (i + 1) / 2)
    (W : ℕ → ℕ → ℝ → ℝ) (s : ℕ) (hW : ∀ k, ContDiff ℝ ∞ (W s k))
    (h0 : W (s + 1) 0 = fun _ => 0)
    (hrec : ∀ k, 1 ≤ k → W (s + 1) k = fun v => deriv (W s k) v + deriv x v * W s (k - 1) v)
    (hbd : BellBound W s) : BellBound W (s + 1) := by
  intro k j u
  rcases k with _ | m
  · rw [h0]
    simp
  · rw [hrec (m + 1) (by omega), Nat.add_sub_cancel]
    exact bell_step hx (hW _) (hW _) hxb s m (hbd (m + 1)) (hbd m) j u

private theorem bellBound_zero (W : ℕ → ℕ → ℝ → ℝ) (h00 : W 0 0 = fun _ => 1)
    (h0k : ∀ k, W 0 (k + 1) = fun _ => 0) : BellBound W 0 := by
  intro k j u
  rcases k with _ | k
  · rw [h00, iteratedDeriv_const]
    rcases j with _ | j <;> simp
  · rw [h0k]
    simp

/-! ## T2: forward differences and derivatives -/

theorem differentiable_fwdDiff_tr {φ : ℝ → ℝ} (h : ℝ) (hφ : Differentiable ℝ φ) :
    Differentiable ℝ (fwdDiff h φ) := by
  show Differentiable ℝ (fun y => φ (y + h) - φ y)
  fun_prop

/-- `|Δ_h φ| ≤ |h| M` if `|φ'| ≤ M` (mean value theorem). -/
theorem abs_fwdDiff_le_of_deriv_tr {φ : ℝ → ℝ} {M : ℝ} (h : ℝ) (hφ : Differentiable ℝ φ)
    (hM : ∀ y, |deriv φ y| ≤ M) (y : ℝ) : |fwdDiff h φ y| ≤ |h| * M := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (fun z _ => hφ z)
    (fun z _ => (Real.norm_eq_abs _).le.trans (hM z)) convex_univ (Set.mem_univ y)
    (Set.mem_univ (y + h))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, show y + h - y = h by ring] at this
  calc |fwdDiff h φ y| = |φ (y + h) - φ y| := rfl
    _ ≤ M * |h| := this
    _ = |h| * M := mul_comm _ _

/-- Differences commute with derivatives: `(Δ_h ψ)^{(j)} = Δ_h ψ^{(j)}`. -/
theorem iteratedDeriv_fwdDiff_tr {ψ : ℝ → ℝ} (h : ℝ) (j : ℕ)
    (hψ : ∀ i < j, Differentiable ℝ (iteratedDeriv i ψ)) :
    iteratedDeriv j (fwdDiff h ψ) = fwdDiff h (iteratedDeriv j ψ) := by
  induction j with
  | zero => simp only [iteratedDeriv_zero]
  | succ j ih =>
    have hd : Differentiable ℝ (iteratedDeriv j ψ) := hψ j (by omega)
    rw [iteratedDeriv_succ, ih (fun i hi => hψ i (by omega)), iteratedDeriv_succ]
    funext y
    have h1 : HasDerivAt (fun z => iteratedDeriv j ψ (z + h))
        (deriv (iteratedDeriv j ψ) (y + h)) y :=
      HasDerivAt.comp_add_const y h (hd (y + h)).hasDerivAt
    exact (h1.sub (hd y).hasDerivAt).deriv

/-- **T2.** `|Δ_h^m ψ| ≤ |h|^m M` if `|ψ^{(m)}| ≤ M` and `ψ^{(i)}` is differentiable for `i < m`
(replaces the `m`-fold integral of D:550 by `m` applications of the mean value theorem). -/
theorem abs_fwdDiff_iter_le_of_iteratedDeriv (h : ℝ) (m : ℕ) :
    ∀ (ψ : ℝ → ℝ) (M : ℝ), (∀ i < m, Differentiable ℝ (iteratedDeriv i ψ)) →
      (∀ y, |iteratedDeriv m ψ y| ≤ M) → ∀ y, |(fwdDiff h)^[m] ψ y| ≤ |h| ^ m * M := by
  induction m with
  | zero => intro ψ M _ hM y; simpa using hM y
  | succ m ih =>
    intro ψ M hd hM y
    have hcomm : ∀ i ≤ m, iteratedDeriv i (fwdDiff h ψ) = fwdDiff h (iteratedDeriv i ψ) :=
      fun i hi => iteratedDeriv_fwdDiff_tr h i (fun k hk => hd k (by omega))
    have hd' : ∀ i < m, Differentiable ℝ (iteratedDeriv i (fwdDiff h ψ)) := by
      intro i hi
      rw [hcomm i hi.le]
      exact differentiable_fwdDiff_tr h (hd i (by omega))
    have hM' : ∀ z, |iteratedDeriv m (fwdDiff h ψ) z| ≤ |h| * M := by
      intro z
      rw [hcomm m le_rfl]
      refine abs_fwdDiff_le_of_deriv_tr h (hd m (by omega)) (fun w => ?_) z
      have := hM w
      rwa [iteratedDeriv_succ] at this
    calc |(fwdDiff h)^[m + 1] ψ y| = |(fwdDiff h)^[m] (fwdDiff h ψ) y| := rfl
      _ ≤ |h| ^ m * (|h| * M) := ih _ _ hd' hM' y
      _ = |h| ^ (m + 1) * M := by ring

/-! ## T3: the representation of `(f ∘ x)^{(t)}` -/

/-- The Bell family: `W_{0,0} = 1`, `W_{0,k+1} = 0`, `W_{t+1,0} = 0`,
`W_{t+1,k+1} = W_{t,k+1}' + x' W_{t,k}`. -/
private def chebW : ℕ → ℕ → ℝ → ℝ
  | 0, 0 => fun _ => 1
  | 0, _ + 1 => fun _ => 0
  | _ + 1, 0 => fun _ => 0
  | t + 1, k + 1 => fun v => deriv (chebW t (k + 1)) v + deriv chebFold v * chebW t k v

private theorem chebW_eq_zero_of_lt : ∀ t k, t < k → chebW t k = fun _ => 0 := by
  intro t
  induction t with
  | zero =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [chebW]
  | succ t ih =>
    intro k hk
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [chebW]
    rw [ih (k + 1) (by omega), ih k (by omega)]
    funext v
    simp

private theorem deriv_chebW_zero (t : ℕ) (u : ℝ) : deriv (chebW t 0) u = 0 := by
  rcases t with _ | t <;> simp [chebW]

private theorem chebW_contDiff : ∀ t k, ContDiff ℝ ∞ (chebW t k) := by
  intro t
  induction t with
  | zero => intro k; rcases k with _ | k <;> exact contDiff_const
  | succ t ih =>
    intro k
    rcases k with _ | k
    · exact contDiff_const
    · simp only [chebW]
      exact (contDiff_infty_iff_deriv.mp (ih (k + 1))).2.add
        ((contDiff_infty_iff_deriv.mp chebFold_contDiff_tr).2.mul (ih k))

private theorem chebW_bound : ∀ t, BellBound chebW t := by
  intro t
  induction t with
  | zero => exact bellBound_zero chebW (by simp only [chebW]) (fun k => by simp only [chebW])
  | succ t ih =>
    refine bellBound_succ chebFold_contDiff_tr abs_iteratedDeriv_succ_chebFold_le chebW t
      (chebW_contDiff t) (by simp only [chebW]) (fun k hk => ?_) ih
    obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [chebW, Nat.add_sub_cancel]

/-- Within-derivative step on `[0,1]`: `f^{(k)}` has derivative `f^{(k+1)}` within `[0,1]`. -/
private theorem hasDerivWithinAt_iteratedDerivWithin_tr {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f (Set.Icc 0 1)) {k : ℕ} (hk : k < n) {y : ℝ}
    (hy : y ∈ Set.Icc (0 : ℝ) 1) :
    HasDerivWithinAt (iteratedDerivWithin k f (Set.Icc 0 1))
      (iteratedDerivWithin (k + 1) f (Set.Icc 0 1) y) (Set.Icc 0 1) y := by
  have hd := hf.differentiableOn_iteratedDerivWithin (by exact_mod_cast hk) uniqueDiffOn_Icc_zero_one
  rw [iteratedDerivWithin_succ]
  exact (hd y hy).hasDerivWithinAt

/-- The index shift of the recurrence, for abstract sequences. -/
private theorem sum_shift_identity (t : ℕ) (F W W' W1 : ℕ → ℝ) (d : ℝ) (hW0 : W' 0 = 0)
    (hWt : W' (t + 1) = 0) (h10 : W1 0 = 0) (h1 : ∀ k, W1 (k + 1) = W' (k + 1) + d * W k) :
    ∑ k ∈ Finset.range (t + 1), (F (k + 1) * d * W k + F k * W' k) =
      ∑ k ∈ Finset.range (t + 1 + 1), F k * W1 k := by
  have e1 : ∑ k ∈ Finset.range (t + 1 + 1), F k * W1 k =
      ∑ k ∈ Finset.range (t + 1), F (k + 1) * W1 (k + 1) + F 0 * W1 0 :=
    Finset.sum_range_succ' (fun k => F k * W1 k) (t + 1)
  have e2 : ∑ k ∈ Finset.range (t + 1), F k * W' k =
      ∑ k ∈ Finset.range t, F (k + 1) * W' (k + 1) + F 0 * W' 0 :=
    Finset.sum_range_succ' (fun k => F k * W' k) t
  have e3 : ∑ k ∈ Finset.range (t + 1), F (k + 1) * W' (k + 1) =
      ∑ k ∈ Finset.range t, F (k + 1) * W' (k + 1) + F (t + 1) * W' (t + 1) :=
    Finset.sum_range_succ (fun k => F (k + 1) * W' (k + 1)) t
  have e4 : ∑ k ∈ Finset.range (t + 1), F (k + 1) * W1 (k + 1) =
      ∑ k ∈ Finset.range (t + 1), F (k + 1) * W' (k + 1) +
        ∑ k ∈ Finset.range (t + 1), F (k + 1) * d * W k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by rw [h1]; ring
  rw [Finset.sum_add_distrib, e1, e2, e4, e3, hW0, hWt, h10]
  ring

private theorem hasDerivAt_rep {f : ℝ → ℝ} {n : ℕ} (hf : ContDiffOn ℝ n f (Set.Icc 0 1))
    (t : ℕ) (ht : t < n) (u : ℝ) :
    HasDerivAt (fun v => ∑ k ∈ Finset.range (t + 1),
        iteratedDerivWithin k f (Set.Icc 0 1) (chebFold v) * chebW t k v)
      (∑ k ∈ Finset.range (t + 1 + 1),
        iteratedDerivWithin k f (Set.Icc 0 1) (chebFold u) * chebW (t + 1) k u) u := by
  have hterm : ∀ k ∈ Finset.range (t + 1),
      HasDerivAt (fun v => iteratedDerivWithin k f (Set.Icc 0 1) (chebFold v) * chebW t k v)
        (iteratedDerivWithin (k + 1) f (Set.Icc 0 1) (chebFold u) * deriv chebFold u *
            chebW t k u +
          iteratedDerivWithin k f (Set.Icc 0 1) (chebFold u) * deriv (chebW t k) u) u := by
    intro k hk
    have hk' : k < n := by have := Finset.mem_range.mp hk; omega
    exact hasDerivAt_comp_chebFold_mul
      (hasDerivWithinAt_iteratedDerivWithin_tr hf hk' (chebFold_mem_Icc_tr u))
      (differentiable_of_smooth (chebW_contDiff t k) u).hasDerivAt
  refine (HasDerivAt.fun_sum hterm).congr_deriv ?_
  exact sum_shift_identity t (fun k => iteratedDerivWithin k f (Set.Icc 0 1) (chebFold u))
    (fun k => chebW t k u) (fun k => deriv (chebW t k) u) (fun k => chebW (t + 1) k u)
    (deriv chebFold u) (deriv_chebW_zero t u)
    (by rw [chebW_eq_zero_of_lt t (t + 1) (by omega)]; simp) (by simp only [chebW])
    (fun k => by simp only [chebW])

/-- **T3.** `(f ∘ x)^{(t)}(u) = Σ_{k ≤ t} f^{(k)}(x(u)) W_{t,k}(u)` for `t ≤ n`, with
derivatives of `f` within `[0,1]`. -/
private theorem iteratedDeriv_comp_chebFold {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f (Set.Icc 0 1)) :
    ∀ t ≤ n, iteratedDeriv t (f ∘ chebFold) = fun u => ∑ k ∈ Finset.range (t + 1),
      iteratedDerivWithin k f (Set.Icc 0 1) (chebFold u) * chebW t k u := by
  intro t
  induction t with
  | zero =>
    intro _
    funext u
    simp [chebW, iteratedDerivWithin_zero]
  | succ t ih =>
    intro ht
    rw [iteratedDeriv_succ, ih (by omega)]
    funext u
    exact (hasDerivAt_rep hf t (by omega) u).deriv

private theorem differentiable_iteratedDeriv_comp {f : ℝ → ℝ} {n : ℕ}
    (hf : ContDiffOn ℝ n f (Set.Icc 0 1)) (t : ℕ) (ht : t < n) :
    Differentiable ℝ (iteratedDeriv t (f ∘ chebFold)) := by
  rw [iteratedDeriv_comp_chebFold hf t ht.le]
  exact fun u => (hasDerivAt_rep hf t ht u).differentiableAt

/-! ## T4: the Hölder bound of the top derivative and the assembly -/

private theorem self_le_rpow_tr {a β : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) : a ≤ a ^ β :=
  calc a = a ^ (1 : ℝ) := (Real.rpow_one a).symm
    _ ≤ a ^ β := Real.rpow_le_rpow_of_exponent_ge' ha0 ha1 hβ0.le hβ1

/-- `min{a, a c} ≤ a^{1-β} (a c)^β = a c^β` (the interpolation of D:546). -/
private theorem le_mul_rpow_of_le_of_le {X a c β : ℝ} (hX : 0 ≤ X) (ha0 : 0 ≤ a) (hc0 : 0 ≤ c)
    (h1 : X ≤ a) (h2 : X ≤ a * c) (hβ0 : 0 < β) (hβ1 : β ≤ 1) : X ≤ a * c ^ β := by
  have hne : (1 - β) + β ≠ 0 := by rw [sub_add_cancel]; exact one_ne_zero
  calc X = X ^ (1 - β) * X ^ β := by rw [← Real.rpow_add' hX hne, sub_add_cancel, Real.rpow_one]
    _ ≤ a ^ (1 - β) * (a * c) ^ β :=
      mul_le_mul (Real.rpow_le_rpow hX h1 (by linarith)) (Real.rpow_le_rpow hX h2 hβ0.le)
        (Real.rpow_nonneg hX _) (Real.rpow_nonneg ha0 _)
    _ = a * c ^ β := by
      rw [Real.mul_rpow ha0 hc0, ← mul_assoc, ← Real.rpow_add' ha0 hne, sub_add_cancel,
        Real.rpow_one]

private theorem chebKappa_eq_sum {s : ℕ} (hs1 : 1 ≤ s) (β : ℝ) :
    chebKappa s β = ∑ k ∈ Finset.range (s + 1),
      (1 + 2 * (k : ℝ) ^ β) * ((2 : ℝ) ^ k)⁻¹ * (Nat.stirlingSecond s k : ℝ) := by
  unfold chebKappa
  split_ifs with h0
  · exact absurd h0 (by omega)
  apply Finset.sum_subset
  · intro k hk
    rw [Finset.mem_Icc] at hk
    rw [Finset.mem_range]
    omega
  · intro k hk hk'
    have hk0 : k = 0 := by
      rw [Finset.mem_range] at hk
      rw [Finset.mem_Icc] at hk'
      omega
    subst hk0
    obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
    have : Nat.stirlingSecond (s' + 1) 0 = 0 := rfl
    simp [this]

private theorem chebKappa_nonneg (s : ℕ) (β : ℝ) : 0 ≤ chebKappa s β := by
  unfold chebKappa
  split_ifs
  · norm_num
  · exact Finset.sum_nonneg fun k _ => by positivity

/-- **Hölder bound of `(f ∘ x)^{(s)}`** (D:540–548):
`|g^{(s)}(u) − g^{(s)}(v)| ≤ π^β (2π)^s κ_{s,β} R |u − v|^β`. -/
private theorem holder_top {f : ℝ → ℝ} {s : ℕ} {β R : ℝ} (hs1 : 1 ≤ s) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hR : 0 ≤ R) (hcont : ContDiffOn ℝ s f (Set.Icc 0 1))
    (hbd : ∀ j ≤ s, ∀ y ∈ Set.Icc (0 : ℝ) 1, |iteratedDerivWithin j f (Set.Icc 0 1) y| ≤ R)
    (hhol : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin s f (Set.Icc 0 1) y - iteratedDerivWithin s f (Set.Icc 0 1) z| ≤
        R * |y - z| ^ β)
    (u v : ℝ) :
    |iteratedDeriv s (f ∘ chebFold) u - iteratedDeriv s (f ∘ chebFold) v| ≤
      π ^ β * (2 * π) ^ s * chebKappa s β * R * |u - v| ^ β := by
  have hrep : ∀ w, iteratedDeriv s (f ∘ chebFold) w = ∑ k ∈ Finset.range (s + 1),
      iteratedDerivWithin k f (Set.Icc 0 1) (chebFold w) * chebW s k w :=
    fun w => congr_fun (iteratedDeriv_comp_chebFold hcont s le_rfl) w
  have hxu := chebFold_mem_Icc_tr u
  have hxv := chebFold_mem_Icc_tr v
  have hdist1 : |chebFold u - chebFold v| ≤ 1 := by
    rw [abs_sub_le_iff]
    constructor <;> linarith [hxu.1, hxu.2, hxv.1, hxv.2]
  have hpow : |chebFold u - chebFold v| ^ β ≤ π ^ β * |u - v| ^ β := by
    rw [← Real.mul_rpow Real.pi_pos.le (abs_nonneg _)]
    exact Real.rpow_le_rpow (abs_nonneg _) (abs_chebFold_sub_le_tr u v) hβ0.le
  rw [hrep u, hrep v, chebKappa_eq_sum hs1, ← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_mul, Finset.sum_mul]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k hk => ?_)
  have hks : k ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  set a := iteratedDerivWithin k f (Set.Icc 0 1) (chebFold u) with ha
  set c := iteratedDerivWithin k f (Set.Icc 0 1) (chebFold v) with hc
  set Ak : ℝ := ((2 : ℝ) ^ k)⁻¹ * (2 * π) ^ s * (Nat.stirlingSecond s k : ℝ) with hAk
  have hAk0 : 0 ≤ Ak := by positivity
  -- the factor `f^{(k)}(x(u)) − f^{(k)}(x(v))`
  have h1 : |a - c| ≤ R * (π ^ β * |u - v| ^ β) := by
    rcases hks.lt_or_eq with hlt | heq
    · have hmvt := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
        (f := iteratedDerivWithin k f (Set.Icc 0 1))
        (f' := fun y => iteratedDerivWithin (k + 1) f (Set.Icc 0 1) y)
        (fun y hy => hasDerivWithinAt_iteratedDerivWithin_tr hcont hlt hy)
        (fun y hy => by rw [Real.norm_eq_abs]; exact hbd (k + 1) (by omega) y hy)
        (convex_Icc 0 1) hxv hxu
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
      calc |a - c| ≤ R * |chebFold u - chebFold v| := hmvt
        _ ≤ R * |chebFold u - chebFold v| ^ β :=
          mul_le_mul_of_nonneg_left (self_le_rpow_tr (abs_nonneg _) hdist1 hβ0 hβ1) hR
        _ ≤ R * (π ^ β * |u - v| ^ β) := mul_le_mul_of_nonneg_left hpow hR
    · rw [ha, hc, heq]
      exact (hhol _ hxu _ hxv).trans (mul_le_mul_of_nonneg_left hpow hR)
  -- the factor `W_{s,k}`
  have h2 : ∀ w, |chebW s k w| ≤ Ak := by
    intro w
    have := chebW_bound s k 0 w
    rw [iteratedDeriv_zero, add_zero, pow_zero, mul_one] at this
    exact this
  have h3 : |c| ≤ R := hbd k hks _ hxv
  have h4 : |chebW s k u - chebW s k v| ≤ 2 * Ak * (π ^ β * (k : ℝ) ^ β * |u - v| ^ β) := by
    have hX2 : |chebW s k u - chebW s k v| ≤ 2 * Ak := by
      calc |chebW s k u - chebW s k v| = |chebW s k u + -chebW s k v| := by rw [sub_eq_add_neg]
        _ ≤ |chebW s k u| + |-chebW s k v| := abs_add_le _ _
        _ ≤ Ak + Ak := by rw [abs_neg]; exact add_le_add (h2 u) (h2 v)
        _ = 2 * Ak := by ring
    have hderiv : ∀ w, |deriv (chebW s k) w| ≤ 2 * Ak * (π * k) := by
      intro w
      have := chebW_bound s k 1 w
      rw [iteratedDeriv_one] at this
      calc |deriv (chebW s k) w| ≤ _ := this
        _ = 2 * Ak * (π * k) := by rw [hAk]; ring
    have hX3 : |chebW s k u - chebW s k v| ≤ 2 * Ak * (π * k * |u - v|) := by
      have hmvt := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun w _ => differentiable_of_smooth (chebW_contDiff s k) w)
        (fun w _ => (Real.norm_eq_abs _).le.trans (hderiv w)) convex_univ (Set.mem_univ v)
        (Set.mem_univ u)
      rw [Real.norm_eq_abs, Real.norm_eq_abs] at hmvt
      calc |chebW s k u - chebW s k v| ≤ 2 * Ak * (π * k) * |u - v| := hmvt
        _ = 2 * Ak * (π * k * |u - v|) := by ring
    have := le_mul_rpow_of_le_of_le (abs_nonneg _) (by positivity) (by positivity) hX2 hX3 hβ0
      hβ1
    rwa [Real.mul_rpow (by positivity) (abs_nonneg _),
      Real.mul_rpow Real.pi_pos.le (Nat.cast_nonneg k)] at this
  calc |a * chebW s k u - c * chebW s k v|
      ≤ |a - c| * |chebW s k u| + |c| * |chebW s k u - chebW s k v| := by
        rw [show a * chebW s k u - c * chebW s k v =
          (a - c) * chebW s k u + c * (chebW s k u - chebW s k v) by ring, ← abs_mul, ← abs_mul]
        exact abs_add_le _ _
    _ ≤ R * (π ^ β * |u - v| ^ β) * Ak + R * (2 * Ak * (π ^ β * (k : ℝ) ^ β * |u - v| ^ β)) :=
        add_le_add (mul_le_mul h1 (h2 u) (abs_nonneg _) (by positivity))
          (mul_le_mul h3 h4 (abs_nonneg _) hR)
    _ = _ := by rw [hAk]; ring

/-- Facts on `s = ⌈α⌉ − 1` and `β = α − s` for `α > 1`. -/
private theorem chebS_facts {α : ℝ} {r : ℕ} (hα1 : 1 < α) (hr : α < r) :
    1 ≤ chebS α ∧ 0 < chebBeta α ∧ chebBeta α ≤ 1 ∧ α = chebS α + chebBeta α ∧
      chebS α + 1 ≤ r := by
  have h1 : 1 < ⌈α⌉₊ := Nat.lt_ceil.mpr (by exact_mod_cast hα1)
  have h2 : ⌈α⌉₊ ≤ r := Nat.ceil_le.mpr hr.le
  have h3 : (⌈α⌉₊ : ℝ) < α + 1 := Nat.ceil_lt_add_one (by linarith)
  have h4 : α ≤ ⌈α⌉₊ := Nat.le_ceil α
  have hcast : ((chebS α : ℕ) : ℝ) = (⌈α⌉₊ : ℝ) - 1 := by
    unfold chebS
    rw [Nat.cast_sub (by omega), Nat.cast_one]
  refine ⟨by unfold chebS; omega, ?_, ?_, by unfold chebBeta; ring, by unfold chebS; omega⟩
  · unfold chebBeta
    rw [hcast]
    linarith
  · unfold chebBeta
    rw [hcast]
    linarith

/-- The case `s ≥ 1` of the transfer, with `r = q + s + 1` (D:549–553). -/
private theorem transfer_core {f : ℝ → ℝ} {s q : ℕ} {α β R : ℝ} (hs1 : 1 ≤ s) (hβ0 : 0 < β)
    (hβ1 : β ≤ 1) (hαsβ : α = s + β) (hcont : ContDiffOn ℝ s f (Set.Icc 0 1))
    (hbd : ∀ j ≤ s, ∀ y ∈ Set.Icc (0 : ℝ) 1, |iteratedDerivWithin j f (Set.Icc 0 1) y| ≤ R)
    (hhol : ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin s f (Set.Icc 0 1) y - iteratedDerivWithin s f (Set.Icc 0 1) z| ≤
        R * |y - z| ^ β) :
    HZBall1 α (q + (s + 1)) ((1 + 2 ^ q * π ^ β * (2 * π) ^ s * chebKappa s β) * R)
      (f ∘ chebFold) := by
  have hsup : ∀ y ∈ Set.Icc (0 : ℝ) 1, |f y| ≤ R := by
    intro y hy
    simpa using hbd 0 (Nat.zero_le _) y hy
  have hR : 0 ≤ R := (abs_nonneg _).trans (hsup 0 (Set.left_mem_Icc.mpr zero_le_one))
  have hκ := chebKappa_nonneg s β
  have hdiff : ∀ i < s, Differentiable ℝ (iteratedDeriv i (f ∘ chebFold)) :=
    fun i hi => differentiable_iteratedDeriv_comp hcont i hi
  refine ⟨hcont.continuousOn.comp_continuous chebFold_contDiff_tr.continuous chebFold_mem_Icc_tr,
    fun u => by simp only [Function.comp_apply, chebFold_periodic_tr u],
    R, 2 ^ q * π ^ β * (2 * π) ^ s * chebKappa s β * R, hR,
    mul_nonneg (mul_nonneg (by positivity) hκ) hR, le_of_eq (by ring),
    fun u => hsup _ (chebFold_mem_Icc_tr u), ?_⟩
  intro h y hh0 _
  rw [fdiff_eq_fwdDiff_iter, Function.iterate_add_apply]
  have hG : ∀ z, |iteratedDeriv s (fwdDiff h (f ∘ chebFold)) z| ≤
      π ^ β * (2 * π) ^ s * chebKappa s β * R * |h| ^ β := by
    intro z
    rw [iteratedDeriv_fwdDiff_tr h s hdiff]
    have := holder_top hs1 hβ0 hβ1 hR hcont hbd hhol (z + h) z
    rw [show z + h - z = h by ring] at this
    exact this
  have hd' : ∀ i < s, Differentiable ℝ (iteratedDeriv i (fwdDiff h (f ∘ chebFold))) := by
    intro i hi
    rw [iteratedDeriv_fwdDiff_tr h i (fun k hk => hdiff k (by omega))]
    exact differentiable_fwdDiff_tr h (hdiff i hi)
  have hM : ∀ z, |(fwdDiff h)^[s + 1] (f ∘ chebFold) z| ≤
      |h| ^ s * (π ^ β * (2 * π) ^ s * chebKappa s β * R * |h| ^ β) :=
    fun z => abs_fwdDiff_iter_le_of_iteratedDeriv h s _ _ hd' hG z
  calc |(fwdDiff h)^[q] ((fwdDiff h)^[s + 1] (f ∘ chebFold)) y|
      ≤ 2 ^ q * (|h| ^ s * (π ^ β * (2 * π) ^ s * chebKappa s β * R * |h| ^ β)) :=
        abs_fwdDiff_iter_le h q _ _ hM y
    _ = 2 ^ q * π ^ β * (2 * π) ^ s * chebKappa s β * R * |h| ^ α := by
        rw [hαsβ, Real.rpow_add hh0, Real.rpow_natCast]
        ring

/-- **The smoothness transfer** (eq:cheb-transfer, D:538–554), for every `0 < α < r`. -/
theorem cheb_transfer {α : ℝ} {r : ℕ} (hα : 0 < α) (hr : α < r) : ChebTransferPremise α r := by
  by_cases hα1 : α ≤ 1
  · exact cheb_transfer_le_one hα hα1 hr
  intro R f hf
  obtain ⟨hcont, hbd, hhol⟩ := hf
  obtain ⟨hs1, hβ0, hβ1, hαsβ, hsr⟩ := chebS_facts (not_le.mp hα1) hr
  obtain ⟨q, hq⟩ : ∃ q, r = q + (chebS α + 1) := ⟨r - (chebS α + 1), by omega⟩
  have hC : chebCtr α r =
      1 + 2 ^ q * π ^ chebBeta α * (2 * π) ^ chebS α * chebKappa (chebS α) (chebBeta α) := by
    rw [chebCtr, show r - chebS α - 1 = q by omega]
  rw [hC, hq]
  exact transfer_core hs1 hβ0 hβ1 hαsβ hcont hbd hhol

/-- `ChebTransferStatement`, with the frozen type. -/
theorem cheb_transfer_statement : ChebTransferStatement :=
  fun _ _ hα hr => cheb_transfer hα hr

end LargePrior
