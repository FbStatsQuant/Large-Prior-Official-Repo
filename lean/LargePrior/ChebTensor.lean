import LargePrior.ChebSpec
import LargePrior.FourierExpand

/-!
# Chebyshev tensorization via the Fourier de la Vallée Poussin smoother

Reduction of the univariate and tensor-product Chebyshev approximation operators
`P_m = Q_{2m − 1}` to the shipped Fourier development (`VdP`, `FourierTensor`, `FourierExpand`):

1. Univariate error bound for `Qop (2 * m - 1)` with the paper's displayed constant
   `chebC α r CJ = max 2 (4 * 3^α * CJ * chebCtr α r)` (D:556–568), keeping the sup-norm bound
   `R` separate from the transferred Hölder–Zygmund radius `chebCtr α r * R`.
2. Generic telescoping error bound for `Pop` with exact per-coordinate weights `3^k` (D:646–650),
   specialised to `chebCapp`.
3. Preservation of coordinatewise evenness and 1-periodicity under `Qop` and `Qcoord`, and
   coordinatewise evenness under `Pop` (`Pop_coordEven`, via internal periodicity).
4. Cosine-only expansion of `Pop (fun k => 2 * m k - 1) g` through the public `Pop_expansion` at
   `M k = m k - 1`, eliminating sine indices by one-coordinate reflection averaging, reindexing
   cosine index `2j − 1` to degree `j`, and zero-padding to `ChebIdx L`.
-/

open MeasureTheory Finset intervalIntegral
open scoped Real

noncomputable section

namespace LargePrior

/-! ## Cosine indexing and atom parity -/

/-- The Fourier atom index corresponding to the `j`-th Chebyshev atom: `0` for `j = 0`, and the
cosine index `2j − 1` for `j ≥ 1`. -/
def chebCosIdx (j : ℕ) : ℕ := if j = 0 then 0 else 2 * j - 1

/-- Predicate selecting constant (`0`) and cosine (`2j − 1`) Fourier indices. -/
def isCosIdx (ν : ℕ) : Prop := ν = 0 ∨ ν % 2 = 1

instance (ν : ℕ) : Decidable (isCosIdx ν) :=
  inferInstanceAs (Decidable (ν = 0 ∨ ν % 2 = 1))

lemma chebCosIdx_zero : chebCosIdx 0 = 0 := rfl

lemma chebCosIdx_of_pos {j : ℕ} (hj : 1 ≤ j) : chebCosIdx j = 2 * j - 1 := by
  unfold chebCosIdx
  have hj0 : j ≠ 0 := by omega
  simp [hj0]

lemma isCosIdx_chebCosIdx (j : ℕ) : isCosIdx (chebCosIdx j) := by
  unfold isCosIdx chebCosIdx
  split_ifs <;> omega

lemma freq_chebCosIdx (j : ℕ) : freq (chebCosIdx j) = j := by
  unfold freq chebCosIdx
  split_ifs <;> omega

lemma chebCosIdx_freq {ν : ℕ} (h : isCosIdx ν) : chebCosIdx (freq ν) = ν := by
  unfold isCosIdx at h
  unfold chebCosIdx freq
  rcases h with rfl | hodd
  · simp
  · have hne : (ν + 1) / 2 ≠ 0 := by omega
    simp only [hne, ↓reduceIte]
    omega

lemma chebCosIdx_lt {m j : ℕ} (hm : 1 ≤ m) (hj : j < m) : chebCosIdx j < 2 * (m - 1) + 1 := by
  unfold chebCosIdx
  split_ifs <;> omega

lemma freq_lt_of_isCosIdx {m ν : ℕ} (hm : 1 ≤ m) (hcos : isCosIdx ν)
    (hν : ν < 2 * (m - 1) + 1) : freq ν < m := by
  unfold isCosIdx at hcos
  unfold freq
  rcases hcos with rfl | hodd <;> omega

lemma chebCosIdx_inj {j₁ j₂ : ℕ} (h : chebCosIdx j₁ = chebCosIdx j₂) : j₁ = j₂ := by
  have := congrArg freq h
  rwa [freq_chebCosIdx, freq_chebCosIdx] at this

lemma fourierAtom_neg_of_cos {ν : ℕ} (h : isCosIdx ν) (t : ℝ) :
    fourierAtom ν (-t) = fourierAtom ν t := by
  unfold isCosIdx at h
  rcases h with rfl | hodd
  · simp [fourierAtom]
  · have h0 : ν ≠ 0 := by omega
    simp only [fourierAtom, h0, hodd, ↓reduceIte]
    rw [show 2 * π * (((ν + 1) / 2 : ℕ) : ℝ) * -t = -(2 * π * (((ν + 1) / 2 : ℕ) : ℝ) * t) by
      ring, Real.cos_neg]

lemma fourierAtom_neg_of_sine {ν : ℕ} (h0 : ν ≠ 0) (hev : ν % 2 = 0) (t : ℝ) :
    fourierAtom ν (-t) = -fourierAtom ν t := by
  have hodd : ¬ ν % 2 = 1 := by omega
  simp only [fourierAtom, h0, hodd, ↓reduceIte]
  rw [show 2 * π * ((ν / 2 : ℕ) : ℝ) * -t = -(2 * π * ((ν / 2 : ℕ) : ℝ) * t) by ring,
    Real.sin_neg, mul_neg]

lemma coef_eq_zero_of_even_periodic {g : ℝ → ℝ} (heven : ∀ t, g (-t) = g t)
    (hper : Function.Periodic g 1) {ν : ℕ} (h0 : ν ≠ 0) (hev : ν % 2 = 0) :
    coef g ν = 0 := by
  unfold coef
  have h1 : ∫ t in (0 : ℝ)..1, g t * fourierAtom ν t =
      ∫ t in (0 : ℝ)..1, g (1 - t) * fourierAtom ν (1 - t) := by
    have hsub := intervalIntegral.integral_comp_sub_left
      (fun t => g t * fourierAtom ν t) (1 : ℝ) (a := (0 : ℝ)) (b := 1)
    norm_num at hsub
    exact hsub.symm
  have h2 : ∀ t, g (1 - t) * fourierAtom ν (1 - t) = -(g t * fourierAtom ν t) := by
    intro t
    have hg : g (1 - t) = g t := by
      rw [show (1 : ℝ) - t = -t + 1 by ring, hper (-t), heven t]
    have hψ : fourierAtom ν (1 - t) = -fourierAtom ν t := by
      rw [show (1 : ℝ) - t = -t + 1 by ring, fourierAtom_periodic ν (-t),
        fourierAtom_neg_of_sine h0 hev t]
    rw [hg, hψ, mul_neg]
  simp_rw [h2, intervalIntegral.integral_neg] at h1
  linarith

/-! ## Univariate error bound for `Qop (2 * m - 1)` (D:556–568) -/

private lemma Qop_one (g : ℝ → ℝ) (u : ℝ) : Qop 1 g u = coef g 0 := by
  simp [Qop, budgetAtoms, qMult, freq, fourierAtom]

private lemma budgetDeg_cheb_bounds {m : ℕ} (hm : 2 ≤ m) :
    1 ≤ budgetDeg (2 * m - 1) ∧ (m : ℝ) / 3 ≤ budgetDeg (2 * m - 1) := by
  refine ⟨by unfold budgetDeg; omega, ?_⟩
  have h : m ≤ 3 * budgetDeg (2 * m - 1) := by unfold budgetDeg; omega
  rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 3)]
  have h' : (m : ℝ) ≤ ((3 * budgetDeg (2 * m - 1) : ℕ) : ℝ) := by exact_mod_cast h
  push_cast at h'
  linarith

/-- **Univariate Chebyshev operator error bound** (D:556–568): for `P_m = Q_{2m−1}`, keeping the
sup-norm bound `|g| ≤ R` separate from the transferred Hölder–Zygmund radius `chebCtr α r * R`
yields the exact displayed constant `chebC α r CJ = max{2, 4 · 3^α C_J C_tr(α)}`. -/
lemma Qop_cheb_error {α : ℝ} {r : ℕ} {CJ R : ℝ} {g : ℝ → ℝ} (hα : 0 < α)
    (hJ : JacksonIneq α r CJ) (hR : ∀ t, |g t| ≤ R) (hHZ : HZBall1 α r (chebCtr α r * R) g)
    {m : ℕ} (hm : 1 ≤ m) (u : ℝ) :
    |g u - Qop (2 * m - 1) g u| ≤ chebC α r CJ * R * (m : ℝ) ^ (-α) := by
  have hgc : Continuous g := hHZ.1
  have hR0 : 0 ≤ R := (abs_nonneg (g 0)).trans (hR 0)
  have hmpos : (0 : ℝ) < m := by exact_mod_cast hm
  have hmα : 0 ≤ (m : ℝ) ^ (-α) := Real.rpow_nonneg hmpos.le _
  rcases eq_or_lt_of_le hm with rfl | hm2
  · -- m = 1: the shipped bound on the constant coefficient plus the pointwise bound on `g`.
    -- D:568 puts the difference under the unit-mass integral first; the estimate is the same.
    rw [show 2 * 1 - 1 = 1 by rfl, Qop_one]
    have h1 : |g u - coef g 0| ≤ 2 * R := by
      have hc0 := coef_abs_le hgc hR 0
      have hgu := hR u
      calc |g u - coef g 0| ≤ |g u| + |coef g 0| := abs_sub _ _
        _ ≤ 2 * R := by linarith
    have h2 : (2 : ℝ) ≤ chebC α r CJ := le_max_left _ _
    simp only [Nat.cast_one, Real.one_rpow, mul_one]
    exact h1.trans (mul_le_mul_of_nonneg_right h2 hR0)
  · have hm2' : 2 ≤ m := hm2
    have hm3 : 3 ≤ 2 * m - 1 := by omega
    obtain ⟨hq1, hq3⟩ := budgetDeg_cheb_bounds hm2'
    obtain ⟨p, hpoly, hp⟩ := hJ (chebCtr α r * R) g hHZ (budgetDeg (2 * m - 1)) hq1
    have hpcont : Continuous p := by
      obtain ⟨c, hpc⟩ := hpoly
      rw [show p = fun y => ∑ ν ∈ range (2 * budgetDeg (2 * m - 1) + 1), c ν * fourierAtom ν y
        from funext hpc]
      exact continuous_finsetSum _ fun ν _ => continuous_const.mul (continuous_fourierAtom ν)
    have hqpos : (0 : ℝ) < budgetDeg (2 * m - 1) := by exact_mod_cast hq1
    have hE : ∀ t, |(g - p) t| ≤ CJ * (chebCtr α r * R) * (budgetDeg (2 * m - 1) : ℝ) ^ (-α) :=
      fun t => by simpa using hp t
    have hstab := Qop_stable (hgc.sub hpcont) hE (2 * m - 1) u
    have hdecomp : g u - Qop (2 * m - 1) g u = (g u - p u) - Qop (2 * m - 1) (g - p) u := by
      rw [Qop_sub hgc hpcont (2 * m - 1) u, Qop_trigPoly hm3 le_rfl hpoly u]
      ring
    have h1 : |g u - Qop (2 * m - 1) g u| ≤
        4 * (CJ * (chebCtr α r * R) * (budgetDeg (2 * m - 1) : ℝ) ^ (-α)) := by
      rw [hdecomp]
      calc |(g u - p u) - Qop (2 * m - 1) (g - p) u|
          ≤ |g u - p u| + |Qop (2 * m - 1) (g - p) u| := abs_sub _ _
        _ ≤ 4 * (CJ * (chebCtr α r * R) * (budgetDeg (2 * m - 1) : ℝ) ^ (-α)) := by
            linarith [hp u]
    have hCR : 0 ≤ CJ * (chebCtr α r * R) :=
      nonneg_of_mul_nonneg_left ((abs_nonneg _).trans (hp u)) (Real.rpow_pos_of_pos hqpos _)
    have hm3pos : (0 : ℝ) < (m : ℝ) / 3 := by positivity
    have h2 : (budgetDeg (2 * m - 1) : ℝ) ^ (-α) ≤ 3 ^ α * (m : ℝ) ^ (-α) := by
      calc (budgetDeg (2 * m - 1) : ℝ) ^ (-α)
          ≤ ((m : ℝ) / 3) ^ (-α) := Real.rpow_le_rpow_of_nonpos hm3pos hq3 (by linarith)
        _ = 3 ^ α * (m : ℝ) ^ (-α) := by
            rw [Real.div_rpow hmpos.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 3),
              div_inv_eq_mul, mul_comm]
    have h4 : 4 * 3 ^ α * CJ * chebCtr α r ≤ chebC α r CJ := le_max_right _ _
    calc |g u - Qop (2 * m - 1) g u|
        ≤ 4 * (CJ * (chebCtr α r * R) * (budgetDeg (2 * m - 1) : ℝ) ^ (-α)) := h1
      _ ≤ 4 * (CJ * (chebCtr α r * R) * (3 ^ α * (m : ℝ) ^ (-α))) := by gcongr
      _ = (4 * 3 ^ α * CJ * chebCtr α r) * (R * (m : ℝ) ^ (-α)) := by ring
      _ ≤ chebC α r CJ * (R * (m : ℝ) ^ (-α)) :=
          mul_le_mul_of_nonneg_right h4 (mul_nonneg hR0 hmα)
      _ = chebC α r CJ * R * (m : ℝ) ^ (-α) := by ring

/-! ## Generic weighted telescoping bound (D:646–650) -/

private lemma foldr_Qcoord_error_weighted {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : Continuous f)
    (n : Fin d → ℕ) (ε : Fin d → ℝ) (hε : ∀ k x, |f x - Qcoord (n k) k f x| ≤ ε k) :
    ∀ κ : List (Fin d),
      Continuous (κ.foldr (fun k g => Qcoord (n k) k g) f) ∧
      ∀ x, |f x - κ.foldr (fun k g => Qcoord (n k) k g) f x| ≤
        ∑ i : Fin κ.length, 3 ^ (i : ℕ) * ε (κ.get i)
  | [] => ⟨hf, fun x => by simp⟩
  | k :: κ => by
    obtain ⟨hcont, hbd⟩ := foldr_Qcoord_error_weighted hf n ε hε κ
    set L := κ.foldr (fun k g => Qcoord (n k) k g) f with hL
    refine ⟨Qcoord_continuous hcont (n k) k, fun x => ?_⟩
    simp only [List.foldr_cons, List.length_cons]
    rw [← hL, Fin.sum_univ_succ]
    have hsub := congrFun (Qcoord_sub hf hcont (n k) k) x
    simp only [Pi.sub_apply] at hsub
    have h1 := hε k x
    have h2 := Qcoord_stable (hf.sub hcont) (fun y => by simpa using hbd y) (n k) k x
    rw [hsub] at h2
    have hsplit : f x - Qcoord (n k) k L x =
        (f x - Qcoord (n k) k f x) + (Qcoord (n k) k f x - Qcoord (n k) k L x) := by ring
    have htail : ∑ i : Fin κ.length, (3 : ℝ) ^ (i.succ : ℕ) * ε ((k :: κ).get i.succ) =
        3 * ∑ i : Fin κ.length, (3 : ℝ) ^ (i : ℕ) * ε (κ.get i) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [Fin.val_succ, pow_succ, List.get_eq_getElem, List.getElem_cons_succ]
      ring
    rw [htail]
    simp only [Fin.val_zero, pow_zero, one_mul, List.get_eq_getElem, List.getElem_cons_zero]
    rw [hsplit]
    exact (abs_add_le _ _).trans (by linarith)

/-- **Generic weighted telescoping bound** (D:646–650): for any continuous `f` and per-coordinate
errors `|f − Q^{(k)}_{n_k} f| ≤ ε_k`, `|f − P_n f| ≤ ∑_k 3^k ε_k` (0-indexed `k : Fin d`, matching
the paper's `3^{k−1}` for `1 ≤ k ≤ d`). -/
lemma Pop_error_weighted {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) (n : Fin d → ℕ)
    (ε : Fin d → ℝ) (hε : ∀ k x, |f x - Qcoord (n k) k f x| ≤ ε k) (x : Fin d → ℝ) :
    |f x - Pop n f x| ≤ ∑ k : Fin d, 3 ^ (k : ℕ) * ε k := by
  have key := (foldr_Qcoord_error_weighted hf n ε hε (List.finRange d)).2 x
  unfold Pop
  refine key.trans (le_of_eq ?_)
  refine Finset.sum_bij (fun i _ => Fin.cast (List.length_finRange) i) (fun _ _ => mem_univ _)
    (fun i₁ _ i₂ _ h => Fin.cast_injective _ h)
    (fun k _ => ⟨Fin.cast (List.length_finRange).symm k, mem_univ _, by simp⟩) fun i _ => ?_
  simp [List.get_eq_getElem]

/-- **Tensor Chebyshev operator error bound** (D:646–650): combining `Qop_cheb_error` in each
coordinate with `Pop_error_weighted` yields the exact displayed constant `chebCapp`. -/
lemma Pop_cheb_error {d : ℕ} (hd : 0 < d) {α : Fin d → ℝ} {r : Fin d → ℕ} {CJ : Fin d → ℝ}
    {R : ℝ} {g : (Fin d → ℝ) → ℝ} (hα : ∀ k, 0 < α k)
    (hJ : ∀ k, JacksonIneq (α k) (r k) (CJ k)) (hg : Continuous g) (hR : ∀ u, |g u| ≤ R)
    (hsec : ∀ k u, HZBall1 (α k) (r k) (chebCtr (α k) (r k) * R) (sectionAt g u k))
    {m : Fin d → ℕ} (hm : ∀ k, 1 ≤ m k) (u : Fin d → ℝ) :
    |g u - Pop (fun k => 2 * m k - 1) g u| ≤
      chebCapp hd α r CJ R * ∑ k, (m k : ℝ) ^ (-α k) := by
  have hR0 : 0 ≤ R := (abs_nonneg (g 0)).trans (hR 0)
  have hε : ∀ k v, |g v - Qcoord (2 * m k - 1) k g v| ≤
      chebCk (α k) (r k) (CJ k) R * (m k : ℝ) ^ (-α k) := by
    intro k v
    have h1 := Qop_cheb_error (hα k) (hJ k) (fun t => hR _) (hsec k v) (hm k) (v k)
    rw [Function.update_eq_self] at h1
    unfold Qcoord sectionAt chebCk
    rw [mul_comm R]
    exact h1
  have key := Pop_error_weighted hg (fun k => 2 * m k - 1)
    (fun k => chebCk (α k) (r k) (CJ k) R * (m k : ℝ) ^ (-α k)) hε u
  refine key.trans ?_
  unfold chebCapp
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun k _ => ?_
  have h3 : (3 : ℝ) ^ (k : ℕ) ≤ 3 ^ (d - 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hck0 : 0 ≤ chebCk (α k) (r k) (CJ k) R :=
    mul_nonneg hR0 ((by norm_num : (0 : ℝ) ≤ 2).trans (le_max_left _ _))
  have hsup : chebCk (α k) (r k) (CJ k) R ≤
      (univ : Finset (Fin d)).sup' ⟨⟨0, hd⟩, mem_univ _⟩
        (fun j => chebCk (α j) (r j) (CJ j) R) :=
    Finset.le_sup' (fun j => chebCk (α j) (r j) (CJ j) R) (mem_univ k)
  have hmα : 0 ≤ (m k : ℝ) ^ (-α k) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hprod : (3 : ℝ) ^ (k : ℕ) * chebCk (α k) (r k) (CJ k) R ≤
      3 ^ (d - 1) * (univ : Finset (Fin d)).sup' ⟨⟨0, hd⟩, mem_univ _⟩
        (fun j => chebCk (α j) (r j) (CJ j) R) :=
    mul_le_mul h3 hsup hck0 (by positivity)
  have := mul_le_mul_of_nonneg_right hprod hmα
  linarith

/-! ## Preservation of evenness and 1-periodicity -/

/-- `Q_n g` is 1-periodic for every `n` and `g`. -/
lemma Qop_periodic (n : ℕ) (g : ℝ → ℝ) : Function.Periodic (Qop n g) 1 := by
  intro u
  unfold Qop
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [fourierAtom_periodic ν u]

/-- `Q_n` preserves evenness on even, 1-periodic functions. -/
lemma Qop_even {g : ℝ → ℝ} (heven : ∀ t, g (-t) = g t) (hper : Function.Periodic g 1)
    (n : ℕ) (u : ℝ) : Qop n g (-u) = Qop n g u := by
  unfold Qop
  refine Finset.sum_congr rfl fun ν _ => ?_
  by_cases hcos : isCosIdx ν
  · rw [fourierAtom_neg_of_cos hcos u]
  · have h0 : ν ≠ 0 := fun h => hcos (Or.inl h)
    have hev : ν % 2 = 0 := by unfold isCosIdx at hcos; omega
    rw [coef_eq_zero_of_even_periodic heven hper h0 hev]
    ring

/-- `Q^{(k)}_n` preserves coordinatewise 1-periodicity. -/
lemma Qcoord_coordPeriodic {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (hper : ∀ i u, f (Function.update u i (u i + 1)) = f u) (n : ℕ) (k : Fin d) :
    ∀ i u, Qcoord n k f (Function.update u i (u i + 1)) = Qcoord n k f u := by
  intro i u
  unfold Qcoord
  by_cases hik : i = k
  · subst hik
    have hsec : sectionAt f (Function.update u i (u i + 1)) i = sectionAt f u i := by
      funext t
      simp [sectionAt, Function.update_idem]
    rw [hsec, Function.update_self, Qop_periodic n (sectionAt f u i) (u i)]
  · have hsec : sectionAt f (Function.update u i (u i + 1)) k = sectionAt f u k := by
      funext t
      unfold sectionAt
      rw [Function.update_comm hik]
      have hi : (Function.update u k t) i = u i := Function.update_of_ne hik _ _
      rw [← hi, hper i (Function.update u k t)]
    rw [hsec, Function.update_of_ne (Ne.symm hik)]

/-- `Q^{(k)}_n` preserves coordinatewise evenness on coordinatewise even, 1-periodic functions. -/
lemma Qcoord_coordEven {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (heven : ∀ i u, f (Function.update u i (-u i)) = f u)
    (hper : ∀ i u, f (Function.update u i (u i + 1)) = f u) (n : ℕ) (k : Fin d) :
    ∀ i u, Qcoord n k f (Function.update u i (-u i)) = Qcoord n k f u := by
  intro i u
  unfold Qcoord
  by_cases hik : i = k
  · subst hik
    have hsec : sectionAt f (Function.update u i (-u i)) i = sectionAt f u i := by
      funext t
      simp [sectionAt, Function.update_idem]
    have hseceven : ∀ t, sectionAt f u i (-t) = sectionAt f u i t := by
      intro t
      unfold sectionAt
      have h1 : Function.update u i (-t) =
          Function.update (Function.update u i t) i (-(Function.update u i t) i) := by
        simp [Function.update_idem]
      rw [h1, heven i]
    have hsecper : Function.Periodic (sectionAt f u i) 1 := by
      intro t
      unfold sectionAt
      have h1 : Function.update u i (t + 1) =
          Function.update (Function.update u i t) i ((Function.update u i t) i + 1) := by
        simp [Function.update_idem]
      rw [h1, hper i]
    rw [hsec, Function.update_self, Qop_even hseceven hsecper n (u i)]
  · have hsec : sectionAt f (Function.update u i (-u i)) k = sectionAt f u k := by
      funext t
      unfold sectionAt
      rw [Function.update_comm hik]
      have hi : (Function.update u k t) i = u i := Function.update_of_ne hik _ _
      rw [← hi, heven i (Function.update u k t)]
    rw [hsec, Function.update_of_ne (Ne.symm hik)]

private lemma foldr_Qcoord_even_periodic {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (heven : ∀ i u, f (Function.update u i (-u i)) = f u)
    (hper : ∀ i u, f (Function.update u i (u i + 1)) = f u) (n : Fin d → ℕ) :
    ∀ κ : List (Fin d),
      (∀ i u, κ.foldr (fun k g => Qcoord (n k) k g) f (Function.update u i (-u i)) =
        κ.foldr (fun k g => Qcoord (n k) k g) f u) ∧
      (∀ i u, κ.foldr (fun k g => Qcoord (n k) k g) f (Function.update u i (u i + 1)) =
        κ.foldr (fun k g => Qcoord (n k) k g) f u)
  | [] => ⟨heven, hper⟩
  | k :: κ => by
    obtain ⟨he, hp⟩ := foldr_Qcoord_even_periodic heven hper n κ
    exact ⟨Qcoord_coordEven he hp (n k) k, Qcoord_coordPeriodic hp (n k) k⟩

/-- `Pop n` preserves coordinatewise evenness on coordinatewise even, 1-periodic functions. -/
lemma Pop_coordEven {d : ℕ} {f : (Fin d → ℝ) → ℝ}
    (heven : ∀ i u, f (Function.update u i (-u i)) = f u)
    (hper : ∀ i u, f (Function.update u i (u i + 1)) = f u) (n : Fin d → ℕ) :
    ∀ i u, Pop n f (Function.update u i (-u i)) = Pop n f u :=
  (foldr_Qcoord_even_periodic heven hper n (List.finRange d)).1

/-! ## Univariate cosine-only expansion (D:556–572) -/

/-- Univariate Chebyshev coefficient map extracted from `Qop (2 * m - 1) g`: for `m ≥ 1` (the
range used by `Qop_cheb_expansion`) it is zero for `j ≥ m`. It is independent of dictionary size
`L`, difference order `r`, and Jackson constant `CJ`. -/
def chebUnivarCoeff (g : ℝ → ℝ) (m j : ℕ) : ℝ :=
  if chebCosIdx j < budgetAtoms (2 * m - 1) then
    qMult (2 * m - 1) j * coef g (chebCosIdx j)
  else 0

/-- **Univariate cosine-only expansion** (D:556–572): for continuous, even, 1-periodic `g` with
`|g| ≤ R` and `m ≥ 1`, `Qop (2 * m - 1) g` expands over cosine atoms `chebCosIdx j` (`j < m`)
with coefficients `ϑ` independent of `L ≥ m`, vanishing for `j ≥ m`, and bounded by `R`. -/
lemma Qop_cheb_expansion {g : ℝ → ℝ} {R : ℝ} (hg : Continuous g) (heven : ∀ t, g (-t) = g t)
    (hper : Function.Periodic g 1) (hR : ∀ t, |g t| ≤ R) {m : ℕ} (hm : 1 ≤ m) :
    ∃ ϑ : ℕ → ℝ, (∀ j, m ≤ j → ϑ j = 0) ∧ (∀ j, |ϑ j| ≤ R) ∧
      ∀ L : ℕ, m ≤ L → ∀ u : ℝ,
        Qop (2 * m - 1) g u = ∑ j ∈ range L, ϑ j * fourierAtom (chebCosIdx j) u := by
  have hR0 : 0 ≤ R := (abs_nonneg (g 0)).trans (hR 0)
  have hba : budgetAtoms (2 * m - 1) ≤ 2 * m - 1 := budgetAtoms_le (by omega)
  refine ⟨chebUnivarCoeff g m, ?_, ?_, ?_⟩
  · intro j hj
    unfold chebUnivarCoeff
    have hnot : ¬ chebCosIdx j < budgetAtoms (2 * m - 1) := by
      rw [chebCosIdx_of_pos (by omega)]
      omega
    simp [hnot]
  · intro j
    unfold chebUnivarCoeff
    split_ifs
    · rw [abs_mul]
      have hq := qMult_mem_Icc (2 * m - 1) j
      have hc := coef_abs_le hg hR (chebCosIdx j)
      rw [abs_of_nonneg hq.1]
      calc qMult (2 * m - 1) j * |coef g (chebCosIdx j)| ≤ 1 * R :=
            mul_le_mul hq.2 hc (abs_nonneg _) zero_le_one
        _ = R := one_mul R
    · simpa using hR0
  · intro L hL u
    have hpad : ∑ j ∈ range L, chebUnivarCoeff g m j * fourierAtom (chebCosIdx j) u =
        ∑ j ∈ (range L).filter (fun j => chebCosIdx j < budgetAtoms (2 * m - 1)),
          qMult (2 * m - 1) j * coef g (chebCosIdx j) * fourierAtom (chebCosIdx j) u := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun j _ => ?_
      unfold chebUnivarCoeff
      split_ifs <;> ring
    have hqop : Qop (2 * m - 1) g u =
        ∑ ν ∈ (range (budgetAtoms (2 * m - 1))).filter isCosIdx,
          qMult (2 * m - 1) (freq ν) * coef g ν * fourierAtom ν u := by
      unfold Qop
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun ν _ => ?_
      by_cases hcos : isCosIdx ν
      · simp [hcos]
      · have h0 : ν ≠ 0 := fun h => hcos (Or.inl h)
        have hev : ν % 2 = 0 := by unfold isCosIdx at hcos; omega
        simp [hcos, coef_eq_zero_of_even_periodic heven hper h0 hev]
    rw [hpad, hqop]
    symm
    refine Finset.sum_bij (fun j _ => chebCosIdx j) ?_ ?_ ?_ ?_
    · intro j hj
      simp only [mem_filter, mem_range] at hj ⊢
      exact ⟨hj.2, isCosIdx_chebCosIdx j⟩
    · intro j₁ _ j₂ _ h
      exact chebCosIdx_inj h
    · intro ν hν
      simp only [mem_filter, mem_range] at hν
      refine ⟨freq ν, ?_, chebCosIdx_freq hν.2⟩
      simp only [mem_filter, mem_range, chebCosIdx_freq hν.2]
      have hνlt : ν < 2 * (m - 1) + 1 := by omega
      exact ⟨lt_of_lt_of_le (freq_lt_of_isCosIdx hm hν.2 hνlt) hL, hν.1⟩
    · intro j _
      rw [freq_chebCosIdx]

/-! ## Multivariate cosine-only expansion by reflection averaging and reindexing (D:653–667) -/

/- Note on departure from the paper (D:659): instead of integrating `g · Ψ_ν` over `𝕋^d` to kill
sine indices, we take the public `Pop_expansion` at `M k = m k - 1` and average `fourierSeries θ`
over single-coordinate reflections `u_i ↦ −u_i` one coordinate at a time. -/

private def maskCoord {d : ℕ} {M : Fin d → ℕ} (i : Fin d) (θ : FourierIdx M → ℝ) :
    FourierIdx M → ℝ :=
  fun ν => if isCosIdx (ν i) then θ ν else 0

private def maskList {d : ℕ} {M : Fin d → ℕ} (κ : List (Fin d)) (θ : FourierIdx M → ℝ) :
    FourierIdx M → ℝ :=
  fun ν => if ∀ k ∈ κ, isCosIdx (ν k) then θ ν else 0

private lemma fourierTensor_update_neg {d : ℕ} (ν : Fin d → ℕ) (i : Fin d) (u : Fin d → ℝ) :
    fourierTensor ν (Function.update u i (-u i)) =
      if isCosIdx (ν i) then fourierTensor ν u else -fourierTensor ν u := by
  unfold fourierTensor
  rw [Fintype.prod_eq_mul_prod_compl i, Fintype.prod_eq_mul_prod_compl i]
  have hcompl : ∏ j ∈ ({i}ᶜ : Finset (Fin d)), fourierAtom (ν j) (Function.update u i (-u i) j) =
      ∏ j ∈ ({i}ᶜ : Finset (Fin d)), fourierAtom (ν j) (u j) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hji : j ≠ i := by simpa using hj
    rw [Function.update_of_ne hji]
  rw [Function.update_self, hcompl]
  split_ifs with hcos
  · rw [fourierAtom_neg_of_cos hcos]
  · have h0 : ν i ≠ 0 := fun h => hcos (Or.inl h)
    have hev : ν i % 2 = 0 := by unfold isCosIdx at hcos; omega
    rw [fourierAtom_neg_of_sine h0 hev, neg_mul]

private lemma fourierSeries_maskCoord {d : ℕ} {M : Fin d → ℕ} (i : Fin d) (θ : FourierIdx M → ℝ)
    (heven : ∀ u, fourierSeries θ (Function.update u i (-u i)) = fourierSeries θ u)
    (u : Fin d → ℝ) :
    fourierSeries (maskCoord i θ) u = fourierSeries θ u := by
  have havg : fourierSeries θ u =
      (fourierSeries θ u + fourierSeries θ (Function.update u i (-u i))) / 2 := by
    rw [heven u]
    ring
  rw [havg]
  unfold fourierSeries maskCoord
  rw [← Finset.sum_add_distrib, Finset.sum_div]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [fourierTensor_update_neg (fun k => (ν k : ℕ)) i u]
  split_ifs <;> ring

private lemma fourierSeries_maskList {d : ℕ} {M : Fin d → ℕ} (θ : FourierIdx M → ℝ)
    (heven : ∀ i u, fourierSeries θ (Function.update u i (-u i)) = fourierSeries θ u) :
    ∀ (κ : List (Fin d)) (u : Fin d → ℝ),
      fourierSeries (maskList κ θ) u = fourierSeries θ u
  | [], u => by
    unfold fourierSeries maskList
    simp
  | i :: κ, u => by
    have ih := fourierSeries_maskList θ heven κ
    have hstep : maskList (i :: κ) θ = maskCoord i (maskList κ θ) := by
      funext ν
      unfold maskList maskCoord
      by_cases hi : isCosIdx (ν i)
      · simp [hi]
      · simp [hi]
    rw [hstep, fourierSeries_maskCoord i (maskList κ θ) (fun v => by rw [ih, ih, heven i v]) u,
      ih u]

/-- Zero-padding of a tensor sum from `ChebIdx m` to `ChebIdx L` when `ϑ` vanishes outside `m`. -/
lemma sum_chebIdx_pad {d : ℕ} {m L : Fin d → ℕ} (hL : ∀ k, m k ≤ L k) (ϑ : (Fin d → ℕ) → ℝ)
    (hsupp : ∀ j, (∃ k, m k ≤ j k) → ϑ j = 0) (φ : (Fin d → ℕ) → ℝ) :
    ∑ j : ChebIdx L, ϑ (fun k => (j k : ℕ)) * φ (fun k => (j k : ℕ)) =
      ∑ j : ChebIdx m, ϑ (fun k => (j k : ℕ)) * φ (fun k => (j k : ℕ)) := by
  have hfilt : ∑ j : ChebIdx L, ϑ (fun k => (j k : ℕ)) * φ (fun k => (j k : ℕ)) =
      ∑ j ∈ (univ : Finset (ChebIdx L)).filter (fun j => ∀ k, (j k : ℕ) < m k),
        ϑ (fun k => (j k : ℕ)) * φ (fun k => (j k : ℕ)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : ∀ k, (j k : ℕ) < m k
    · simp [hj]
    · push Not at hj
      simp [show ¬ ∀ k, (j k : ℕ) < m k from fun h => by
        obtain ⟨k, hk⟩ := hj; exact (lt_irrefl _) (lt_of_lt_of_le (h k) hk),
        hsupp (fun k => (j k : ℕ)) hj]
  rw [hfilt]
  symm
  refine Finset.sum_bij (fun j _ k => Fin.castLE (hL k) (j k)) ?_ ?_ ?_ ?_
  · intro j _
    simp only [mem_filter, mem_univ, true_and, Fin.val_castLE]
    exact fun k => (j k).isLt
  · intro j₁ _ j₂ _ h
    funext k
    exact Fin.ext (by simpa using congrArg (fun f : ChebIdx L => (f k : ℕ)) h)
  · intro j hj
    simp only [mem_filter, mem_univ, true_and] at hj
    refine ⟨fun k => ⟨(j k : ℕ), hj k⟩, mem_univ _, ?_⟩
    funext k
    exact Fin.ext rfl
  · intro j _
    rfl

/-- **Multivariate cosine-only expansion of `Pop (fun k => 2 * m k - 1) g`** (D:653–667):
via public `Pop_expansion` at `M k = m k - 1`, reflection averaging removes all sine indices,
reindexing `chebCosIdx` maps cosine indices to degrees `< m k`, and zero-padding extends the sum
to every `L ≥ m` with the same coefficient map `ϑ`. -/
lemma Pop_cheb_expansion {d : ℕ} {g : (Fin d → ℝ) → ℝ} {R : ℝ} (hg : Continuous g)
    (heven : ∀ i u, g (Function.update u i (-u i)) = g u)
    (hper : ∀ i u, g (Function.update u i (u i + 1)) = g u) (hR : ∀ u, |g u| ≤ R)
    {m : Fin d → ℕ} (hm : ∀ k, 1 ≤ m k) :
    ∃ ϑ : (Fin d → ℕ) → ℝ, (∀ j, (∃ k, m k ≤ j k) → ϑ j = 0) ∧ (∀ j, |ϑ j| ≤ R) ∧
      ∀ L : Fin d → ℕ, (∀ k, m k ≤ L k) → ∀ u : Fin d → ℝ,
        Pop (fun k => 2 * m k - 1) g u =
          ∑ j : ChebIdx L, ϑ (fun k => (j k : ℕ)) *
            fourierTensor (fun k => chebCosIdx (j k)) u := by
  have hR0 : 0 ≤ R := (abs_nonneg (g 0)).trans (hR 0)
  have hm' : ∀ k, 1 ≤ 2 * m k - 1 ∧ 2 * m k - 1 ≤ 2 * (m k - 1) + 1 :=
    fun k => ⟨by have := hm k; omega, by have := hm k; omega⟩
  obtain ⟨θ, -, hθ, hP⟩ := Pop_expansion hg hR (fun k => m k - 1) (fun k => 2 * m k - 1) hm'
  have hθeven : ∀ i u, fourierSeries θ (Function.update u i (-u i)) = fourierSeries θ u := by
    intro i u
    rw [← hP, ← hP]
    exact Pop_coordEven heven hper (fun k => 2 * m k - 1) i u
  have hmask : ∀ u, Pop (fun k => 2 * m k - 1) g u =
      fourierSeries (maskList (List.finRange d) θ) u := by
    intro u
    rw [hP u, fourierSeries_maskList θ hθeven (List.finRange d) u]
  let ϑ : (Fin d → ℕ) → ℝ := fun j =>
    if h : ∀ k, j k < m k then
      θ (fun k => ⟨chebCosIdx (j k), chebCosIdx_lt (hm k) (h k)⟩)
    else 0
  have hsupp : ∀ j, (∃ k, m k ≤ j k) → ϑ j = 0 := by
    intro j ⟨k, hk⟩
    have hnot : ¬ ∀ k', j k' < m k' := fun h => not_lt_of_ge hk (h k)
    dsimp only [ϑ]
    exact dite_eq_right hnot
  refine ⟨ϑ, hsupp, ?_, ?_⟩
  · intro j
    by_cases hj : ∀ k, j k < m k
    · dsimp only [ϑ]
      rw [dite_eq_left hj]
      exact hθ _
    · dsimp only [ϑ]
      rw [dite_eq_right hj, abs_zero]
      exact hR0
  · intro L hL u
    rw [sum_chebIdx_pad hL ϑ hsupp (fun j => fourierTensor (fun k => chebCosIdx (j k)) u),
      hmask u]
    unfold fourierSeries maskList
    have hfilt : ∑ ν : FourierIdx (fun k => m k - 1),
        (if ∀ k ∈ List.finRange d, isCosIdx (ν k) then θ ν else 0) *
          fourierTensor (fun k => (ν k : ℕ)) u =
        ∑ ν ∈ (univ : Finset (FourierIdx (fun k => m k - 1))).filter
            (fun ν => ∀ k, isCosIdx (ν k)),
          θ ν * fourierTensor (fun k => (ν k : ℕ)) u := by
      rw [Finset.sum_filter]
      refine Finset.sum_congr rfl fun ν _ => ?_
      simp only [List.mem_finRange, true_implies]
      split_ifs <;> ring
    rw [hfilt]
    symm
    refine Finset.sum_bij
      (fun (j : ChebIdx m) _ k => ⟨chebCosIdx (j k), chebCosIdx_lt (hm k) (j k).isLt⟩)
      ?_ ?_ ?_ ?_
    · intro j _
      simp only [mem_filter, mem_univ, true_and]
      exact fun k => isCosIdx_chebCosIdx (j k)
    · intro j₁ _ j₂ _ h
      funext k
      exact Fin.ext (chebCosIdx_inj (by
        simpa using congrArg (fun f : FourierIdx (fun k => m k - 1) => (f k : ℕ)) h))
    · intro ν hν
      simp only [mem_filter, mem_univ, true_and] at hν
      refine ⟨fun k => ⟨freq (ν k), freq_lt_of_isCosIdx (hm k) (hν k) (ν k).isLt⟩, mem_univ _, ?_⟩
      funext k
      exact Fin.ext (chebCosIdx_freq (hν k))
    · intro j _
      have hj : ∀ k, (j k : ℕ) < m k := fun k => (j k).isLt
      dsimp only [ϑ]
      rw [dite_eq_left hj]

end LargePrior
