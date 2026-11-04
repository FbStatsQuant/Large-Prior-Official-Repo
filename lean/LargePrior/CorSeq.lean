import LargePrior.CorSeqA

/-!
# Corollary 1: sequence asymptotics (blueprint §B.3–B.4)

Steps 2–3 of the proof of Corollary 1 that concern only the deterministic sequences
`N_n, m_{n,k}, a_n, ε̃_n, δ_n, s_n, ε_n` (no dictionary, no prior).
-/

open Filter Finset
open scoped Topology

noncomputable section

namespace LargePrior

/-! ### Helpers -/

/-- `n / log n → ∞` along the naturals. -/
private lemma tendsto_nat_div_log :
    Tendsto (fun n : ℕ => (n : ℝ) / Real.log n) atTop atTop := by
  have h1 : Tendsto (fun x : ℝ => x / Real.log x) atTop atTop := by
    rw [tendsto_atTop]
    intro b
    have hε : (0 : ℝ) < 1 / (|b| + 1) := by positivity
    filter_upwards [Real.isLittleO_log_id_atTop.bound hε, eventually_gt_atTop (1 : ℝ)]
      with x hx hx1
    have hlog : 0 < Real.log x := Real.log_pos hx1
    rw [Real.norm_of_nonneg hlog.le, id, Real.norm_of_nonneg (by linarith)] at hx
    rw [le_div_iff₀ hlog]
    have h2 : (|b| + 1) * Real.log x ≤ x := by
      have := mul_le_mul_of_nonneg_left hx (by positivity : (0 : ℝ) ≤ |b| + 1)
      rwa [← mul_assoc, mul_one_div_cancel (by positivity), one_mul] at this
    nlinarith [le_abs_self b]
  exact h1.comp tendsto_natCast_atTop_atTop

/-- Basic eventual facts: `n ≥ 2`, `J_n ≥ 3`, `log J_n ≥ 1`, `log n > 0`, and
`(n / log n)/C₁ ≤ N_n ≤ (n / log n)/c₁`. -/
private lemma seq_base {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∃ c1 C1 : ℝ, 0 < c1 ∧ 0 < C1 ∧ ∀ᶠ n : ℕ in atTop,
      2 ≤ n ∧ 3 ≤ J n ∧ 1 ≤ Real.log (J n) ∧ 0 < Real.log n ∧
      (n : ℝ) / Real.log n / C1 ≤ corN n (J n) ∧
      corN n (J n) ≤ (n : ℝ) / Real.log n / c1 := by
  obtain ⟨hJ, c, C, hc, hev⟩ := logJ_comparable h
  refine ⟨c, max C 1, hc, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  filter_upwards [hev, eventually_ge_atTop 2, hJ.eventually_ge_atTop 3] with n hn hn2 hJ3
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlogn : 0 < Real.log n := Real.log_pos hn1
  have hlogJ : 1 ≤ Real.log (J n) := by
    have h3 : (3 : ℝ) ≤ J n := by exact_mod_cast hJ3
    have he : Real.exp 1 ≤ 3 := by
      have := Real.exp_one_lt_d9
      norm_num at this ⊢
      linarith
    calc (1 : ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (J n) := Real.log_le_log (Real.exp_pos 1) (he.trans h3)
  refine ⟨hn2, hJ3, hlogJ, hlogn, ?_, ?_⟩
  · unfold corN
    rw [div_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by linarith)
    calc Real.log (J n) ≤ C * Real.log n := hn.2
      _ ≤ max C 1 * Real.log n := mul_le_mul_of_nonneg_right (le_max_left _ _) hlogn.le
      _ = Real.log n * max C 1 := mul_comm _ _
  · unfold corN
    rw [div_div]
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (mul_pos hlogn hc)
    rw [mul_comm]
    exact hn.1

/-- `N_n → ∞`. -/
private lemma tendsto_corN {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    Tendsto (fun n : ℕ => corN n (J n)) atTop atTop := by
  obtain ⟨c1, C1, -, hC1, hev⟩ := seq_base h
  refine tendsto_atTop_mono' atTop ?_ (tendsto_nat_div_log.atTop_div_const hC1)
  filter_upwards [hev] with n hn using hn.2.2.2.2.1

/-- `∏_k x^{β_k} = x^D` for `x > 0`. -/
private lemma prod_rpow_beta {d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k)
    {x : ℝ} (hx : 0 < x) : ∏ k, x ^ betaExp α k = x ^ dimExp α := by
  rw [← Real.rpow_sum_of_pos hx, (exponent_identities hd hα).2.1]

/-- `x^D / x = (x^{-r})²` for `x > 0` (since `D - 1 = -2r`). -/
private lemma rpow_D_div {d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k)
    {x : ℝ} (hx : 0 < x) : x ^ dimExp α / x = (x ^ (-rateExp α)) ^ 2 := by
  rw [← Real.rpow_sub_one hx.ne', ← Real.rpow_natCast, ← Real.rpow_mul hx.le]
  congr 1
  have := (exponent_identities hd hα).2.2
  push_cast
  linarith

/-- `⌈x⌉₊ ≤ 2x` for `x ≥ 1`. -/
private lemma ceil_le_two_mul {x : ℝ} (hx : 1 ≤ x) : (⌈x⌉₊ : ℝ) ≤ 2 * x := by
  exact Nat.ceil_le_two_mul (le_trans (by norm_num : (2 : ℝ)⁻¹ ≤ 1) hx)

/-- For `N ≥ 1`: `C_sp N^D ≤ a ≤ C_sp 2^d N^D + 1`. -/
private lemma corA_bounds {d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k) {Csp : ℝ}
    (hCsp : 0 < Csp) {n J : ℕ} (hN : 1 ≤ corN n J) :
    Csp * corN n J ^ dimExp α ≤ corA Csp α n J ∧
      (corA Csp α n J : ℝ) ≤ Csp * 2 ^ d * corN n J ^ dimExp α + 1 := by
  have hN0 : 0 < corN n J := by linarith
  have hβ := (exponents_pos hd hα).2.2.2.2
  have hm : ∀ k, corN n J ^ betaExp α k ≤ corM α n J k ∧
      (corM α n J k : ℝ) ≤ 2 * corN n J ^ betaExp α k := fun k =>
    ⟨Nat.le_ceil _, ceil_le_two_mul (Real.one_le_rpow hN (hβ k).le)⟩
  constructor
  · calc Csp * corN n J ^ dimExp α = Csp * ∏ k, corN n J ^ betaExp α k := by
          rw [prod_rpow_beta hd hα hN0]
      _ ≤ Csp * ∏ k, (corM α n J k : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hCsp.le
          exact Finset.prod_le_prod₀ (fun k _ => (Real.rpow_pos_of_pos hN0 _).le)
            (fun k _ => (hm k).1)
      _ ≤ corA Csp α n J := Nat.le_ceil _
  · have hprod : 0 ≤ Csp * ∏ k, (corM α n J k : ℝ) := by positivity
    calc (corA Csp α n J : ℝ) ≤ Csp * ∏ k, (corM α n J k : ℝ) + 1 :=
          (Nat.ceil_lt_add_one hprod).le
      _ ≤ Csp * ∏ k, (2 * corN n J ^ betaExp α k) + 1 := by
          apply add_le_add_left
          apply mul_le_mul_of_nonneg_left _ hCsp.le
          exact Finset.prod_le_prod₀ (fun k _ => Nat.cast_nonneg _) (fun k _ => (hm k).2)
      _ = Csp * 2 ^ d * corN n J ^ dimExp α + 1 := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
            prod_rpow_beta hd hα hN0]
          ring

/-- For every `ε > 0`, eventually `m_{n,k} ≤ ε n^{b_k}` for all `k`. -/
private lemma corM_small {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ k, (corM α n (J n) k : ℝ) ≤ ε * (n : ℝ) ^ b k := by
  obtain ⟨c1, C1, -, -, hev⟩ := seq_base h
  have hβ := (exponents_pos h.hd h.hα).2.2.2.2
  have hlogJ : Tendsto (fun n : ℕ => Real.log (J n)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp (logJ_comparable h).1)
  have hk : ∀ k, ∀ᶠ n : ℕ in atTop, 2 / ε ≤ Real.log (J n) ^ betaExp α k := fun k =>
    ((tendsto_rpow_atTop (hβ k)).comp hlogJ).eventually_ge_atTop _
  filter_upwards [hev, (tendsto_corN h).eventually_ge_atTop 1, eventually_all.2 hk]
    with n hn hN hkn k
  obtain ⟨hn2, -, hlogJ1, -, -, -⟩ := hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (by omega : 1 ≤ n)
  have hX : 0 < Real.log (J n) ^ betaExp α k := Real.rpow_pos_of_pos (by linarith) _
  have hnb : 0 < (n : ℝ) ^ b k := Real.rpow_pos_of_pos (by linarith) _
  have h2 : 2 ≤ Real.log (J n) ^ betaExp α k * ε := (div_le_iff₀ hε).1 (hkn k)
  calc (corM α n (J n) k : ℝ) ≤ 2 * corN n (J n) ^ betaExp α k :=
        ceil_le_two_mul (Real.one_le_rpow hN (hβ k).le)
    _ = 2 * ((n : ℝ) ^ betaExp α k / Real.log (J n) ^ betaExp α k) := by
        rw [corN, Real.div_rpow (Nat.cast_nonneg _) (by linarith)]
    _ ≤ 2 * ((n : ℝ) ^ b k / Real.log (J n) ^ betaExp α k) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply div_le_div_of_nonneg_right _ hX.le
        exact Real.rpow_le_rpow_of_exponent_le hn1 (h.hb k)
    _ ≤ ε * (n : ℝ) ^ b k := by
        rw [← mul_div_assoc, div_le_iff₀ hX]
        nlinarith [mul_le_mul_of_nonneg_left h2 hnb.le]

/-- Two-sided bounds with constant `K` transfer to any larger constant `C`. -/
private lemma two_sided_mono {K C x y : ℝ} (hK : 0 < K) (hKC : K ≤ C) (hx : 0 ≤ x)
    (h1 : K⁻¹ * x ≤ y) (h2 : y ≤ K * x) : C⁻¹ * x ≤ y ∧ y ≤ C * x := by
  have hinv : C⁻¹ ≤ K⁻¹ := inv_anti₀ hK hKC
  exact ⟨(mul_le_mul_of_nonneg_right hinv hx).trans h1,
    h2.trans (mul_le_mul_of_nonneg_right hKC hx)⟩

/-- Eventual facts about the chosen sequences (blueprint B.3, Step 2 and G4): `J_n ≥ 2`,
`N_n ≥ 1`, `1 ≤ m_{n,k} ≤ L_{n,k}`, `1 ≤ a_n ≤ J_n`, `ε̃_n > 0`, `0 < δ_n ≤ ε̃_n / J_n`. -/
lemma seq_eventually {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∀ᶠ n : ℕ in atTop, 2 ≤ J n ∧ 1 ≤ corN n (J n) ∧
      (∀ k, 1 ≤ corM α n (J n) k ∧ corM α n (J n) k ≤ L n k) ∧
      1 ≤ corA Csp α n (J n) ∧ corA Csp α n (J n) ≤ J n ∧
      0 < corEpsT Ceps α n (J n) ∧ 0 < corDelta cδ Ceps α n (J n) ∧
      corDelta cδ Ceps α n (J n) ≤ corEpsT Ceps α n (J n) / J n := by
  obtain ⟨c, C, hc, hsz⟩ := h.hsize
  obtain ⟨c1, C1, -, -, hb⟩ := seq_base h
  have hε : 0 < min 1 (c / Csp) := lt_min one_pos (div_pos hc h.hCsp)
  filter_upwards [hb, (tendsto_corN h).eventually_ge_atTop 1, hsz,
    corM_small h (mul_pos hε hc)] with n hn hN hs hm
  obtain ⟨-, hJ3, -⟩ := hn
  have hN0 : 0 < corN n (J n) := by linarith
  have hJ0 : (0 : ℝ) < J n := by exact_mod_cast (by omega : 0 < J n)
  -- `m_{n,k} ≤ ε L_{n,k}` with `ε = min 1 (c / C_sp)`
  have hmL : ∀ k, (corM α n (J n) k : ℝ) ≤ min 1 (c / Csp) * L n k := fun k =>
    calc (corM α n (J n) k : ℝ) ≤ min 1 (c / Csp) * c * (n : ℝ) ^ b k := hm k
      _ = min 1 (c / Csp) * (c * (n : ℝ) ^ b k) := by ring
      _ ≤ min 1 (c / Csp) * L n k := mul_le_mul_of_nonneg_left (hs.1 k).1 hε.le
  have hm1 : ∀ k, 1 ≤ corM α n (J n) k := fun k =>
    Nat.one_le_ceil_iff.2 (Real.rpow_pos_of_pos hN0 _)
  have hεT : 0 < corEpsT Ceps α n (J n) := mul_pos h.hCeps (Real.rpow_pos_of_pos hN0 _)
  refine ⟨by omega, hN, fun k => ⟨hm1 k, ?_⟩, ?_, ?_, hεT, ?_, ?_⟩
  · have : (corM α n (J n) k : ℝ) ≤ L n k :=
      (hmL k).trans (mul_le_of_le_one_left (Nat.cast_nonneg _) (min_le_left _ _))
    exact_mod_cast this
  · apply Nat.one_le_ceil_iff.2
    apply mul_pos h.hCsp
    exact Finset.prod_pos (fun k _ => by exact_mod_cast hm1 k)
  · apply Nat.ceil_le.2
    have hpow : min 1 (c / Csp) ^ d ≤ min 1 (c / Csp) :=
      pow_le_of_le_one hε.le (min_le_left _ _) (by have := h.hd; omega)
    have hCε : Csp * min 1 (c / Csp) ≤ c := by
      calc Csp * min 1 (c / Csp) ≤ Csp * (c / Csp) :=
            mul_le_mul_of_nonneg_left (min_le_right _ _) h.hCsp.le
        _ = c := mul_div_cancel₀ c h.hCsp.ne'
    have hL0 : 0 ≤ ∏ k, (L n k : ℝ) := by positivity
    calc Csp * ∏ k, (corM α n (J n) k : ℝ) ≤ Csp * ∏ k, (min 1 (c / Csp) * L n k) := by
          apply mul_le_mul_of_nonneg_left _ h.hCsp.le
          exact Finset.prod_le_prod₀ (fun k _ => Nat.cast_nonneg _) (fun k _ => hmL k)
      _ = Csp * (min 1 (c / Csp) ^ d * ∏ k, (L n k : ℝ)) := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ ≤ Csp * (min 1 (c / Csp) * ∏ k, (L n k : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ h.hCsp.le
          exact mul_le_mul_of_nonneg_right hpow hL0
      _ = (Csp * min 1 (c / Csp)) * ∏ k, (L n k : ℝ) := by ring
      _ ≤ c * ∏ k, (L n k : ℝ) := mul_le_mul_of_nonneg_right hCε hL0
      _ ≤ J n := hs.2.1
  · exact div_pos (mul_pos h.hcδ hεT) hJ0
  · exact div_le_div_of_nonneg_right (mul_le_of_le_one_left hεT.le h.hcδ1.le) hJ0.le

/-- `a_n ≍ N_n^D`: `C_sp N_n^D ≤ a_n ≤ C N_n^D` for large `n` (blueprint B.4). -/
lemma corA_comparable {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      Csp * corN n (J n) ^ dimExp α ≤ corA Csp α n (J n) ∧
      (corA Csp α n (J n) : ℝ) ≤ C * corN n (J n) ^ dimExp α := by
  have hD := (exponents_pos h.hd h.hα).2.2.1
  have hCsp := h.hCsp
  refine ⟨Csp * 2 ^ d + 1, by positivity, ?_⟩
  filter_upwards [(tendsto_corN h).eventually_ge_atTop 1] with n hN
  obtain ⟨h1, h2⟩ := corA_bounds h.hd h.hα h.hCsp hN
  have hND : 1 ≤ corN n (J n) ^ dimExp α := Real.one_le_rpow hN hD.le
  refine ⟨h1, ?_⟩
  calc (corA Csp α n (J n) : ℝ) ≤ Csp * 2 ^ d * corN n (J n) ^ dimExp α + 1 := h2
    _ ≤ Csp * 2 ^ d * corN n (J n) ^ dimExp α + corN n (J n) ^ dimExp α := by linarith
    _ = (Csp * 2 ^ d + 1) * corN n (J n) ^ dimExp α := by ring

/-- `n ε̃_n² → ∞` (standing requirement). -/
lemma tendsto_n_epsT_sq {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    Tendsto (fun n : ℕ => (n : ℝ) * corEpsT Ceps α n (J n) ^ 2) atTop atTop := by
  have hD := (exponents_pos h.hd h.hα).2.2.1
  have hC2 : 0 < Ceps ^ 2 := pow_pos h.hCeps 2
  have hND : Tendsto (fun n : ℕ => Ceps ^ 2 * corN n (J n) ^ dimExp α) atTop atTop :=
    ((tendsto_rpow_atTop hD).comp (tendsto_corN h)).const_mul_atTop hC2
  obtain ⟨c1, C1, -, -, hev⟩ := seq_base h
  refine tendsto_atTop_mono' atTop ?_ hND
  filter_upwards [hev, (tendsto_corN h).eventually_ge_atTop 1] with n hn hN
  obtain ⟨hn2, hJ3, hlogJ, -⟩ := hn
  rw [n_epsT_sq_eq h.hd h.hα Ceps (by omega) (by omega)]
  have hX : 0 ≤ Ceps ^ 2 * corN n (J n) ^ dimExp α :=
    mul_nonneg hC2.le (Real.rpow_nonneg (by linarith) _)
  exact le_mul_of_one_le_right hX hlogJ

/-! ### Explicit constants of eq:cor-constants (cor_v2, W2) -/

/-- `0 < A' = A C_s / C_sp` for `A ≥ 1`. -/
lemma corAprime_pos {A d : ℕ} {Csp Ceps : ℝ} (hA : 1 ≤ A) (hCsp : 0 < Csp) :
    0 < corAprime A d Csp Ceps := by
  have hCa : 0 < corCa d Csp := by unfold corCa; positivity
  have hCs : 0 < corCs d Csp Ceps := lt_of_lt_of_le hCa (le_max_left _ _)
  have hA' : (0 : ℝ) < A := by exact_mod_cast hA
  unfold corAprime
  positivity

/-- `0 < c = C_ε² / C_a`. -/
lemma corExpConst_pos {d : ℕ} {Csp Ceps : ℝ} (hCsp : 0 < Csp) (hCeps : 0 < Ceps) :
    0 < corExpConst d Csp Ceps := by
  have hCa : 0 < corCa d Csp := by unfold corCa; positivity
  unfold corExpConst
  positivity

/-- Translation 3 of Appendix B: `A s_n ≤ A' a_n` for all large `n`
(from `s_n ≤ C_s N_n^D` and `C_sp N_n^D ≤ a_n`). -/
lemma cor_sRate_le_Aprime {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) (A : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      ((A * sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℕ) : ℝ) ≤
        corAprime A d Csp Ceps * corA Csp α n (J n) := by
  obtain ⟨c1, C1, -, -, hb⟩ := seq_base h
  have hD := (exponents_pos h.hd h.hα).2.2.1
  have hCa : 0 < corCa d Csp := by unfold corCa; have := h.hCsp; positivity
  have hCs : 0 < corCs d Csp Ceps := lt_of_lt_of_le hCa (le_max_left _ _)
  filter_upwards [hb, (tendsto_corN h).eventually_ge_atTop 1] with n hn hN
  obtain ⟨hn2, hJ3, hlogJ, -⟩ := hn
  have hN0 : 0 < corN n (J n) := by linarith
  have hND : 1 ≤ corN n (J n) ^ dimExp α := Real.one_le_rpow hN hD.le
  have hX : 0 ≤ Ceps ^ 2 * corN n (J n) ^ dimExp α :=
    mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hN0.le _)
  have hNDnn : 0 ≤ corN n (J n) ^ dimExp α := by linarith
  have hceil : ((⌈(n : ℝ) * corEpsT Ceps α n (J n) ^ 2 / Real.log (J n)⌉₊ : ℕ) : ℝ) ≤
      (Ceps ^ 2 + 1) * corN n (J n) ^ dimExp α := by
    rw [n_epsT_sq_eq h.hd h.hα Ceps (by omega) (by omega), mul_div_assoc,
      div_self (by linarith), mul_one]
    have := Nat.ceil_lt_add_one hX
    nlinarith
  have hcs1 : corCa d Csp ≤ corCs d Csp Ceps := le_max_left _ _
  have hcs2 : Ceps ^ 2 + 1 ≤ corCs d Csp Ceps := le_max_right _ _
  have hup := (corA_bounds h.hd h.hα h.hCsp hN).2
  have hlow := (corA_bounds h.hd h.hα h.hCsp hN).1
  have hs : (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) ≤
      corCs d Csp Ceps * corN n (J n) ^ dimExp α := by
    unfold sRate
    rw [Nat.cast_max]
    apply max_le
    · have : (corA Csp α n (J n) : ℝ) ≤ corCa d Csp * corN n (J n) ^ dimExp α := by
        unfold corCa
        nlinarith
      exact this.trans (mul_le_mul_of_nonneg_right hcs1 hNDnn)
    · exact hceil.trans (mul_le_mul_of_nonneg_right hcs2 hNDnn)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg _
  rw [Nat.cast_mul]
  calc (A : ℝ) * (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ)
      ≤ A * (corCs d Csp Ceps * corN n (J n) ^ dimExp α) :=
        mul_le_mul_of_nonneg_left hs hA0
    _ ≤ A * (corCs d Csp Ceps * (corA Csp α n (J n) / Csp)) := by
        apply mul_le_mul_of_nonneg_left _ hA0
        apply mul_le_mul_of_nonneg_left _ hCs.le
        rw [le_div_iff₀ h.hCsp]
        linarith
    _ = corAprime A d Csp Ceps * corA Csp α n (J n) := by
        unfold corAprime
        ring

/-- Translation 2 of Appendix B: `c a_n log J_n ≤ n ε̃_n²` for all large `n`, with
`c = C_ε² / C_a`, `C_a = 2^d C_sp + 1`. -/
lemma cor_exp_lower_explicit {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∀ᶠ n : ℕ in atTop,
      corExpConst d Csp Ceps * corA Csp α n (J n) * Real.log (J n) ≤
        (n : ℝ) * corEpsT Ceps α n (J n) ^ 2 := by
  obtain ⟨c1, C1, -, -, hb⟩ := seq_base h
  have hD := (exponents_pos h.hd h.hα).2.2.1
  have hCsp := h.hCsp
  have hCa : 0 < corCa d Csp := by unfold corCa; positivity
  have hC2 : 0 < Ceps ^ 2 := pow_pos h.hCeps 2
  filter_upwards [hb, (tendsto_corN h).eventually_ge_atTop 1] with n hn hN
  obtain ⟨hn2, hJ3, hlogJ, -⟩ := hn
  have hND : 1 ≤ corN n (J n) ^ dimExp α := Real.one_le_rpow hN hD.le
  have hup := (corA_bounds h.hd h.hα h.hCsp hN).2
  rw [n_epsT_sq_eq h.hd h.hα Ceps (by omega) (by omega)]
  have hle : corExpConst d Csp Ceps * corA Csp α n (J n) ≤
      Ceps ^ 2 * corN n (J n) ^ dimExp α := by
    unfold corExpConst
    rw [div_mul_eq_mul_div, div_le_iff₀ hCa]
    have : (corA Csp α n (J n) : ℝ) ≤ corCa d Csp * corN n (J n) ^ dimExp α := by
      unfold corCa
      nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hC2.le]
  exact mul_le_mul_of_nonneg_right hle (by linarith)


/-- `s_n ≤ C_s N_n^D` eventually. -/
private lemma sRate_le {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∃ Cs : ℝ, 0 < Cs ∧ ∀ᶠ n : ℕ in atTop,
      (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) ≤
        Cs * corN n (J n) ^ dimExp α := by
  obtain ⟨Ca, hCa, ha⟩ := corA_comparable h
  have hAprime := corAprime_pos (d := d) (Ceps := Ceps) le_rfl h.hCsp
  refine ⟨corAprime 1 d Csp Ceps * Ca, mul_pos hAprime hCa, ?_⟩
  filter_upwards [cor_sRate_le_Aprime h 1, ha] with n hs hn
  simp only [one_mul] at hs
  exact hs.trans (by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_left hn.2 hAprime.le)

/-- `s_n log J_n / n → 0` (standing requirement). -/
lemma tendsto_sRate_log {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    Tendsto (fun n : ℕ => (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) *
      Real.log (J n) / n) atTop (𝓝 0) := by
  obtain ⟨Cs, hCs, hev⟩ := sRate_le h
  obtain ⟨c1, C1, -, -, hb⟩ := seq_base h
  have hD1 : 0 < 1 - dimExp α := by linarith [(exponents_pos h.hd h.hα).2.2.2.1]
  have hlim : Tendsto (fun n : ℕ => Cs * corN n (J n) ^ (-(1 - dimExp α))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop hD1).comp (tendsto_corN h)).const_mul Cs
    rw [mul_zero] at this
    exact this
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
  · filter_upwards [hb] with n hn
    obtain ⟨-, -, hlogJ, -⟩ := hn
    exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith)) (Nat.cast_nonneg _)
  · filter_upwards [hev, (tendsto_corN h).eventually_ge_atTop 1] with n hs hN
    have hN0 : 0 < corN n (J n) := by linarith
    have hratio : (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) *
        Real.log (J n) / n =
        (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) / corN n (J n) := by
      rw [corN, div_div_eq_mul_div]
    rw [hratio, show -(1 - dimExp α) = dimExp α - 1 by ring, Real.rpow_sub_one hN0.ne',
      ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hs hN0.le

/-- `n ε̃_n² ≳ a_n log J_n`: some `c > 0` has `c a_n log J_n ≤ n ε̃_n²` for large `n`. -/
lemma cor_exp_lower {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * corA Csp α n (J n) * Real.log (J n) ≤ (n : ℝ) * corEpsT Ceps α n (J n) ^ 2 := by
  exact ⟨corExpConst d Csp Ceps, corExpConst_pos h.hCsp h.hCeps,
    cor_exp_lower_explicit h⟩

/-- `a_n ≍ (n / log n)^D`. -/
private lemma orders_a {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      K⁻¹ * ((n : ℝ) / Real.log n) ^ dimExp α ≤ corA Csp α n (J n) ∧
      (corA Csp α n (J n) : ℝ) ≤ K * ((n : ℝ) / Real.log n) ^ dimExp α := by
  obtain ⟨Ca, hCa, hev⟩ := corA_comparable h
  obtain ⟨c1, C1, hc1, hC1, hb⟩ := seq_base h
  have hD := (exponents_pos h.hd h.hα).2.2.1
  have hC1D : 0 < C1 ^ dimExp α := Real.rpow_pos_of_pos hC1 _
  have hc1D : 0 < c1 ^ dimExp α := Real.rpow_pos_of_pos hc1 _
  have hK1 : 0 < C1 ^ dimExp α / Csp := div_pos hC1D h.hCsp
  have hK2 : 0 < Ca / c1 ^ dimExp α := div_pos hCa hc1D
  refine ⟨C1 ^ dimExp α / Csp + Ca / c1 ^ dimExp α, add_pos hK1 hK2, ?_⟩
  filter_upwards [hev, hb] with n ha hn
  obtain ⟨-, -, -, hlogn, hlo, hup⟩ := hn
  have hP0 : 0 ≤ (n : ℝ) / Real.log n := div_nonneg (Nat.cast_nonneg _) hlogn.le
  have hPD : 0 ≤ ((n : ℝ) / Real.log n) ^ dimExp α := Real.rpow_nonneg hP0 _
  have hlowD : ((n : ℝ) / Real.log n) ^ dimExp α / C1 ^ dimExp α ≤
      corN n (J n) ^ dimExp α := by
    rw [← Real.div_rpow hP0 hC1.le]
    exact Real.rpow_le_rpow (div_nonneg hP0 hC1.le) hlo hD.le
  have hupD : corN n (J n) ^ dimExp α ≤
      ((n : ℝ) / Real.log n) ^ dimExp α / c1 ^ dimExp α := by
    rw [← Real.div_rpow hP0 hc1.le]
    exact Real.rpow_le_rpow ((div_nonneg hP0 hC1.le).trans hlo) hup hD.le
  constructor
  · have hinv : (C1 ^ dimExp α / Csp + Ca / c1 ^ dimExp α)⁻¹ ≤ Csp / C1 ^ dimExp α := by
      calc (C1 ^ dimExp α / Csp + Ca / c1 ^ dimExp α)⁻¹ ≤ (C1 ^ dimExp α / Csp)⁻¹ :=
            inv_anti₀ hK1 (le_add_of_nonneg_right hK2.le)
        _ = Csp / C1 ^ dimExp α := inv_div _ _
    calc (C1 ^ dimExp α / Csp + Ca / c1 ^ dimExp α)⁻¹ * ((n : ℝ) / Real.log n) ^ dimExp α
        ≤ Csp / C1 ^ dimExp α * ((n : ℝ) / Real.log n) ^ dimExp α :=
          mul_le_mul_of_nonneg_right hinv hPD
      _ = Csp * (((n : ℝ) / Real.log n) ^ dimExp α / C1 ^ dimExp α) := by ring
      _ ≤ Csp * corN n (J n) ^ dimExp α := mul_le_mul_of_nonneg_left hlowD h.hCsp.le
      _ ≤ corA Csp α n (J n) := ha.1
  · calc (corA Csp α n (J n) : ℝ) ≤ Ca * corN n (J n) ^ dimExp α := ha.2
      _ ≤ Ca * (((n : ℝ) / Real.log n) ^ dimExp α / c1 ^ dimExp α) :=
          mul_le_mul_of_nonneg_left hupD hCa.le
      _ = Ca / c1 ^ dimExp α * ((n : ℝ) / Real.log n) ^ dimExp α := by ring
      _ ≤ (C1 ^ dimExp α / Csp + Ca / c1 ^ dimExp α) * ((n : ℝ) / Real.log n) ^ dimExp α :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hK1.le) hPD

/-- `ε_n ≍ (n / log n)^{-r}`. -/
private lemma orders_eps {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ n : ℕ in atTop,
      K⁻¹ * corRate α n ≤ epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ∧
      epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ≤ K * corRate α n := by
  obtain ⟨Cs, hCs, hev⟩ := sRate_le h
  obtain ⟨c1, C1, hc1, hC1, hb⟩ := seq_base h
  have hr := (exponents_pos h.hd h.hα).2.1
  have hu : 0 < C1 ^ (-rateExp α) := Real.rpow_pos_of_pos hC1 _
  have hl : 0 < c1 ^ (-rateExp α) := Real.rpow_pos_of_pos hc1 _
  have hCs' : 0 < Real.sqrt Cs := Real.sqrt_pos.2 hCs
  have hCsp' : 0 < Real.sqrt Csp := Real.sqrt_pos.2 h.hCsp
  have hKu0 : 0 < Real.sqrt Cs / C1 ^ (-rateExp α) := div_pos hCs' hu
  have hKl0 : 0 < Real.sqrt Csp / c1 ^ (-rateExp α) := div_pos hCsp' hl
  refine ⟨Real.sqrt Cs / C1 ^ (-rateExp α) + (Real.sqrt Csp / c1 ^ (-rateExp α))⁻¹,
    add_pos hKu0 (inv_pos.2 hKl0), ?_⟩
  filter_upwards [hev, hb, (tendsto_corN h).eventually_ge_atTop 1] with n hs hn hN
  obtain ⟨hn2, -, -, hlogn, hlo, hup⟩ := hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hN0 : 0 < corN n (J n) := by linarith
  have hP0 : 0 < (n : ℝ) / Real.log n := div_pos hn0 hlogn
  have hQ0 : 0 ≤ corN n (J n) ^ (-rateExp α) := Real.rpow_nonneg hN0.le _
  have hR0 : 0 ≤ corRate α n := Real.rpow_nonneg hP0.le _
  have hQu : corN n (J n) ^ (-rateExp α) ≤ corRate α n / C1 ^ (-rateExp α) := by
    rw [corRate, ← Real.div_rpow hP0.le hC1.le]
    exact Real.rpow_le_rpow_of_nonpos (div_pos hP0 hC1) hlo (by linarith)
  have hQl : corRate α n / c1 ^ (-rateExp α) ≤ corN n (J n) ^ (-rateExp α) := by
    rw [corRate, ← Real.div_rpow hP0.le hc1.le]
    exact Real.rpow_le_rpow_of_nonpos hN0 hup (by linarith)
  have hratio : (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) *
      Real.log (J n) / n =
      (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) / corN n (J n) := by
    rw [corN, div_div_eq_mul_div]
  have hsN0 : 0 ≤ (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) /
      corN n (J n) := div_nonneg (Nat.cast_nonneg _) hN0.le
  have hsu : (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) /
      corN n (J n) ≤ Cs * (corN n (J n) ^ (-rateExp α)) ^ 2 := by
    rw [← rpow_D_div h.hd h.hα hN0, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right hs hN0.le
  have hsl : Csp * (corN n (J n) ^ (-rateExp α)) ^ 2 ≤
      (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) / corN n (J n) := by
    rw [← rpow_D_div h.hd h.hα hN0, ← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hN0.le
    calc Csp * corN n (J n) ^ dimExp α ≤ corA Csp α n (J n) :=
          (corA_bounds h.hd h.hα h.hCsp hN).1
      _ ≤ (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) := by
          exact_mod_cast le_max_left _ _
  unfold epsRate
  rw [hratio]
  constructor
  · have hinv : (Real.sqrt Cs / C1 ^ (-rateExp α) + (Real.sqrt Csp / c1 ^ (-rateExp α))⁻¹)⁻¹ ≤
        Real.sqrt Csp / c1 ^ (-rateExp α) := by
      calc (Real.sqrt Cs / C1 ^ (-rateExp α) + (Real.sqrt Csp / c1 ^ (-rateExp α))⁻¹)⁻¹
          ≤ ((Real.sqrt Csp / c1 ^ (-rateExp α))⁻¹)⁻¹ :=
            inv_anti₀ (inv_pos.2 hKl0) (le_add_of_nonneg_left hKu0.le)
        _ = Real.sqrt Csp / c1 ^ (-rateExp α) := inv_inv _
    calc (Real.sqrt Cs / C1 ^ (-rateExp α) + (Real.sqrt Csp / c1 ^ (-rateExp α))⁻¹)⁻¹ *
          corRate α n ≤ Real.sqrt Csp / c1 ^ (-rateExp α) * corRate α n :=
          mul_le_mul_of_nonneg_right hinv hR0
      _ = Real.sqrt Csp * (corRate α n / c1 ^ (-rateExp α)) := by ring
      _ ≤ Real.sqrt Csp * corN n (J n) ^ (-rateExp α) :=
          mul_le_mul_of_nonneg_left hQl hCsp'.le
      _ ≤ _ := by
          rw [Real.le_sqrt (mul_nonneg hCsp'.le hQ0) hsN0, mul_pow, Real.sq_sqrt h.hCsp.le]
          exact hsl
  · calc Real.sqrt ((sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) /
          corN n (J n)) ≤ Real.sqrt Cs * corN n (J n) ^ (-rateExp α) := by
          rw [Real.sqrt_le_iff]
          refine ⟨mul_nonneg hCs'.le hQ0, ?_⟩
          rw [mul_pow, Real.sq_sqrt hCs.le]
          exact hsu
      _ ≤ Real.sqrt Cs * (corRate α n / C1 ^ (-rateExp α)) :=
          mul_le_mul_of_nonneg_left hQu hCs'.le
      _ = Real.sqrt Cs / C1 ^ (-rateExp α) * corRate α n := by ring
      _ ≤ (Real.sqrt Cs / C1 ^ (-rateExp α) + (Real.sqrt Csp / c1 ^ (-rateExp α))⁻¹) *
          corRate α n :=
          mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (inv_pos.2 hKl0).le) hR0

/-- The orders of `s_n`, `a_n`, `ε_n` (first part of `CorConclusion`; G1, G2). -/
lemma cor_orders {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      (corA Csp α n (J n) : ℝ) ≤ sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ∧
      (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) ≤
        C * corA Csp α n (J n) ∧
      C⁻¹ * ((n : ℝ) / Real.log n) ^ dimExp α ≤ corA Csp α n (J n) ∧
      (corA Csp α n (J n) : ℝ) ≤ C * ((n : ℝ) / Real.log n) ^ dimExp α ∧
      C⁻¹ * corRate α n ≤ epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ∧
      epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ≤ C * corRate α n := by
  obtain ⟨K1, hK1, h1⟩ := orders_a h
  obtain ⟨K2, hK2, h2⟩ := orders_eps h
  obtain ⟨Cs, hCs, hs⟩ := sRate_le h
  obtain ⟨c1, C1, -, -, hb⟩ := seq_base h
  have hK3 : 0 < Cs / Csp := div_pos hCs h.hCsp
  refine ⟨K1 + K2 + Cs / Csp, by linarith, ?_⟩
  filter_upwards [h1, h2, hs, hb, (tendsto_corN h).eventually_ge_atTop 1]
    with n ha he hsn hn hN
  obtain ⟨hn2, -, -, hlogn, -⟩ := hn
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hP0 : 0 < (n : ℝ) / Real.log n := div_pos hn0 hlogn
  have hPD : 0 ≤ ((n : ℝ) / Real.log n) ^ dimExp α := Real.rpow_nonneg hP0.le _
  have hR0 : 0 ≤ corRate α n := Real.rpow_nonneg hP0.le _
  obtain ⟨ha1, ha2⟩ := two_sided_mono (C := K1 + K2 + Cs / Csp) hK1 (by linarith) hPD ha.1 ha.2
  obtain ⟨he1, he2⟩ := two_sided_mono (C := K1 + K2 + Cs / Csp) hK2 (by linarith) hR0 he.1 he.2
  refine ⟨by exact_mod_cast le_max_left _ _, ?_, ha1, ha2, he1, he2⟩
  have hlow := (corA_bounds h.hd h.hα h.hCsp hN).1
  calc (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ)
      ≤ Cs * corN n (J n) ^ dimExp α := hsn
    _ ≤ Cs * (corA Csp α n (J n) / Csp) := by
        apply mul_le_mul_of_nonneg_left _ hCs.le
        rw [le_div_iff₀ h.hCsp]
        linarith
    _ = Cs / Csp * corA Csp α n (J n) := by ring
    _ ≤ (K1 + K2 + Cs / Csp) * corA Csp α n (J n) :=
        mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _)

/-- `ε̃_n → 0` (G3; not used by Theorem 1, recorded for inspection). -/
lemma tendsto_corEpsT {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    Tendsto (fun n : ℕ => corEpsT Ceps α n (J n)) atTop (𝓝 0) := by
  have := ((tendsto_rpow_neg_atTop (exponents_pos h.hd h.hα).2.1).comp
    (tendsto_corN h)).const_mul Ceps
  rw [mul_zero] at this
  exact this


end LargePrior
