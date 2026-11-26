import LargePrior.Corollary
import LargePrior.HorseshoeAsymptotic
import LargePrior.Horseshoe

/-!
# Corollary 1 with the horseshoe prior

The horseshoe with `τ_n = J_n^{−(2+μ'')}/√n` satisfies Assumption 3 for the corollary's
sequences, by the existing translation of Wei and Ghosal (2020), Theorem 3.3
(`horseshoe_assumption3`).
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

/-- Inverse-radius bound: `log(1/ε̃_n) ≤ (|log C_ε| + r) log n`. -/
private lemma log_inv_epsT_le {d : ℕ} {α : Fin d → ℝ} {Ceps : ℝ} (hC : 0 < Ceps)
    (hr : 0 ≤ rateExp α) {n J : ℕ} (hn : 0 < n) (hN : 1 ≤ corN n J) (hlogJ : 1 ≤ Real.log J)
    (hlogn : 1 ≤ Real.log n) :
    Real.log (1 / corEpsT Ceps α n J) ≤ (|Real.log Ceps| + rateExp α) * Real.log n := by
  have hNpos : 0 < corN n J := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hNn : corN n J ≤ n := by
    unfold corN
    exact div_le_self hnR.le hlogJ
  have hlogN : Real.log (corN n J) ≤ Real.log n := Real.log_le_log hNpos hNn
  rw [one_div, Real.log_inv, corEpsT, Real.log_mul hC.ne' (Real.rpow_pos_of_pos hNpos _).ne',
    Real.log_rpow hNpos]
  have h1 : 0 ≤ |Real.log Ceps| * (Real.log n - 1) := mul_nonneg (abs_nonneg _) (by linarith)
  have h2 : 0 ≤ rateExp α * (Real.log n - Real.log (corN n J)) := mul_nonneg hr (by linarith)
  have h3 := neg_abs_le (Real.log Ceps)
  nlinarith

/-- Inverse-scale bound: `log(1/τ_n) = (2 + μ'') log J_n + ½ log n`. -/
private lemma log_inv_tau_eq {μ'' : ℝ} {n J : ℕ} (hn : 0 < n) (hJ : 0 < J) :
    Real.log (1 / corTau μ'' n J) = (2 + μ'') * Real.log J + Real.log n / 2 := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hp : 0 < (J : ℝ) ^ (-(2 + μ'')) := Real.rpow_pos_of_pos hJR _
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.2 hnR
  rw [one_div, Real.log_inv, corTau, Real.log_div hp.ne' hs.ne', Real.log_rpow hJR,
    Real.log_sqrt hnR.le]
  ring

/-- The budget conditions of `HorseshoeAssumption3Statement` for the corollary's sequences:
some `B ≥ 0` has, for large `n`, `a_n log J_n ≤ B n ε̃_n²`, `log(1/ε̃_n) ≤ B log J_n`,
`log(1/τ_n) ≤ B log J_n`, `log E ≤ B log J_n`. -/
lemma cor_horseshoe_budget {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) {E μ'' : ℝ} (hE : 0 < E)
    (hμ'' : 0 < μ'') :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ᶠ n : ℕ in atTop,
      (corA Csp α n (J n) : ℝ) * Real.log (J n) ≤ B * n * corEpsT Ceps α n (J n) ^ 2 ∧
      Real.log (1 / corEpsT Ceps α n (J n)) ≤ B * Real.log (J n) ∧
      Real.log (1 / corTau μ'' n (J n)) ≤ B * Real.log (J n) ∧
      Real.log E ≤ B * Real.log (J n) := by
  -- Positivity of `E` is retained in the API; the budget bound only needs `|log E|`.
  have _ := hE
  obtain ⟨hJtop, c1, C1, hc1, hlog⟩ := logJ_comparable h
  obtain ⟨Ca, hCa, hA⟩ := corA_comparable h
  have hev := seq_eventually h
  obtain ⟨_, hr, _⟩ := exponents_pos h.hd h.hα
  have hCe := h.hCeps
  set B1 : ℝ := Ca / Ceps ^ 2 with hB1
  set B2 : ℝ := (|Real.log Ceps| + rateExp α) / c1 with hB2
  set B3 : ℝ := 2 + μ'' + 1 / (2 * c1) with hB3
  set B4 : ℝ := |Real.log E| with hB4
  have hB1n : 0 ≤ B1 := by positivity
  have hB2n : 0 ≤ B2 := by positivity
  have hB3n : 0 ≤ B3 := by positivity
  have hB4n : 0 ≤ B4 := abs_nonneg _
  refine ⟨B1 + B2 + B3 + B4, by positivity, ?_⟩
  filter_upwards [hev, hA, hlog, hJtop.eventually_ge_atTop 3, eventually_ge_atTop 3]
    with n hn hAn hln hJ3 hn3
  obtain ⟨hJ2, hN, -, -, -, -, -, -⟩ := hn
  obtain ⟨_, hAupper⟩ := hAn
  obtain ⟨hlogLower, _⟩ := hln
  have hnpos : 0 < n := by omega
  have hnR : (0 : ℝ) < n := by exact_mod_cast hnpos
  have hJR3 : (3 : ℝ) ≤ J n := by exact_mod_cast hJ3
  have hexp : Real.exp 1 < 3 := by linarith [Real.exp_one_lt_d9]
  have hlogJ1 : 1 ≤ Real.log (J n) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith
  have hlogn1 : 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnR]
    have : (3 : ℝ) ≤ n := by exact_mod_cast hn3
    linarith
  have hnJ : Real.log n ≤ Real.log (J n) / c1 := by
    rw [le_div_iff₀ hc1]
    linarith [hlogLower]
  have hne := n_epsT_sq_eq h.hd h.hα Ceps hnpos (by omega : 1 < J n)
  have hnn : 0 ≤ (n : ℝ) * corEpsT Ceps α n (J n) ^ 2 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- bound 1
    have hl0 : 0 ≤ Real.log (J n) := by linarith
    have h1 : (corA Csp α n (J n) : ℝ) * Real.log (J n) ≤
        Ca * corN n (J n) ^ dimExp α * Real.log (J n) :=
      mul_le_mul_of_nonneg_right hAupper hl0
    have h2 : Ca * corN n (J n) ^ dimExp α * Real.log (J n) =
        B1 * ((n : ℝ) * corEpsT Ceps α n (J n) ^ 2) := by
      rw [hne, hB1]
      field_simp
    have h3 : B1 * ((n : ℝ) * corEpsT Ceps α n (J n) ^ 2) ≤
        (B1 + B2 + B3 + B4) * n * corEpsT Ceps α n (J n) ^ 2 := by
      have := mul_le_mul_of_nonneg_right (by linarith : B1 ≤ B1 + B2 + B3 + B4) hnn
      linarith
    linarith
  · -- bound 2
    have h1 := log_inv_epsT_le (α := α) hCe hr.le hnpos hN hlogJ1 hlogn1
    have h2 : (|Real.log Ceps| + rateExp α) * Real.log n ≤ B2 * Real.log (J n) := by
      have hnum : 0 ≤ |Real.log Ceps| + rateExp α := by positivity
      calc (|Real.log Ceps| + rateExp α) * Real.log n
          ≤ (|Real.log Ceps| + rateExp α) * (Real.log (J n) / c1) :=
            mul_le_mul_of_nonneg_left hnJ hnum
        _ = B2 * Real.log (J n) := by rw [hB2]; ring
    have h3 : B2 * Real.log (J n) ≤ (B1 + B2 + B3 + B4) * Real.log (J n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith
  · -- bound 3
    rw [log_inv_tau_eq hnpos (by omega)]
    have h1 : Real.log n / 2 ≤ 1 / (2 * c1) * Real.log (J n) := by
      have : Real.log n / 2 ≤ Real.log (J n) / c1 / 2 := by linarith
      calc Real.log n / 2 ≤ Real.log (J n) / c1 / 2 := this
        _ = 1 / (2 * c1) * Real.log (J n) := by field_simp
    have h3 : B3 * Real.log (J n) ≤ (B1 + B2 + B3 + B4) * Real.log (J n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have h4 : B3 * Real.log (J n) = (2 + μ'') * Real.log (J n) + 1 / (2 * c1) * Real.log (J n) := by
      rw [hB3]; ring
    linarith
  · -- bound 4
    have h1 : Real.log E ≤ B4 := le_abs_self _
    have h2 : B4 ≤ B4 * Real.log (J n) := le_mul_of_one_le_right hB4n hlogJ1
    have h3 : B4 * Real.log (J n) ≤ (B1 + B2 + B3 + B4) * Real.log (J n) :=
      mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    linarith

/-- `τ_n > 0` for large `n`. -/
lemma corTau_pos {μ'' : ℝ} {J : ℕ → ℕ} (hJ : ∀ᶠ n in atTop, 1 ≤ J n) :
    ∀ᶠ n : ℕ in atTop, 0 < corTau μ'' n (J n) := by
  filter_upwards [hJ, eventually_ge_atTop 1] with n hJn hn
  unfold corTau
  have hJpos : (0 : ℝ) < J n := by exact_mod_cast hJn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (Real.rpow_pos_of_pos hJpos _) (Real.sqrt_pos.2 hnpos)

/-- The horseshoe hypotheses give `CorHyp` with `μ = μ''/2`, `c₄ = 1`, `c₅ = B(6 + 5B)`. -/
lemma CorHorseshoeHyp.corHyp {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ} {f₀ : ∀ n : ℕ, Fin n → ℝ} {σ : ℝ}
    {Csp Capp E Ceps cδ K η μ'' : ℝ}
    (h : CorHorseshoeHyp α b L J X f₀ σ Csp Capp E Ceps cδ K η μ'') :
    ∃ c5 : ℝ, 0 ≤ c5 ∧ CorHyp α b L J X f₀ σ (fun n => horseshoePDF (corTau μ'' n (J n)))
      Csp Capp E Ceps cδ K η (μ'' / 2) 1 c5 := by
  have hs : SeqHyp α b L J Csp Ceps cδ :=
    ⟨h.hd, h.hα, h.hb, h.hsize, h.hCsp, h.hCeps, h.hcδ, h.hcδ1⟩
  obtain ⟨B, hB, hbud⟩ := cor_horseshoe_budget hs h.hE h.hμ''
  have hev := seq_eventually hs
  obtain ⟨hJtop, -⟩ := logJ_comparable hs
  have hJ1 : ∀ᶠ n in atTop, 1 ≤ J n := hev.mono fun n ⟨hJ2, _⟩ => by omega
  have hτ := corTau_pos (μ'' := μ'') hJ1
  have h3 := horseshoe_assumption3 J (fun n => corEpsT Ceps α n (J n))
    (fun n => corDelta cδ Ceps α n (J n)) (fun _ => E) (fun n => corTau μ'' n (J n))
    (fun n => corA Csp α n (J n)) η μ'' cδ 1 B hJtop (tendsto_n_epsT_sq hs)
    h.hη h.hμ'' h.hcδ one_pos hB
    (hev.mono fun _ ⟨_, _, _, ha, haJ, _, _, _⟩ => ⟨ha, haJ⟩)
    (hev.mono fun _ ⟨_, _, _, _, _, hεt, _, _⟩ => hεt)
    (Eventually.of_forall fun _ => h.hE) hτ
    (Eventually.of_forall fun n => by unfold corDelta; exact le_refl _)
    (Eventually.of_forall fun n => by unfold corTau; rw [one_mul])
    (hbud.mono fun n ⟨hb1, hb2, hb3, hb4⟩ => ⟨by simpa [mul_assoc] using hb1, hb2, hb3, hb4⟩)
  refine ⟨B * (6 + 5 * B), by positivity, ?_⟩
  exact
    { hd := h.hd, hα := h.hα, hb := h.hb, hsize := h.hsize, hσ := h.hσ, hK := h.hK
      hbasis := h.hbasis, hCsp := h.hCsp, hCapp := h.hCapp, hE := h.hE, hprofile := h.hprofile
      hCeps := h.hCeps, hCepsApp := h.hCepsApp, hcδ := h.hcδ, hcδ1 := h.hcδ1, hη := h.hη
      hη1 := h.hη1, hμ := by linarith [h.hμ''], hc4 := zero_le_one, hc5 := by positivity
      hpdf := hτ.mono fun n hn => horseshoe_isProbDensity _ hn
      h3 := h3.mono fun n ⟨hWG3, _⟩ => hWG3
      h4 := (h3.and hev).mono fun n hn => by
        obtain ⟨⟨-, hWG4, -⟩, -, -, -, -, haJ, -, -, -⟩ := hn
        obtain ⟨S, -, hS⟩ := Finset.exists_subset_card_eq
          (s := (Finset.univ : Finset (Fin (J n)))) (n := corA Csp α n (J n))
          (by rw [Finset.card_univ, Fintype.card_fin]; exact haJ)
        exact ⟨S, hS, hWG4 S hS⟩
      h5 := h3.mono fun n ⟨_, _, h5n⟩ => h5n }

/-- **Corollary 1 for the horseshoe prior.** -/
theorem cor_horseshoe : CorHorseshoeStatement := by
  intro d α b L J X f₀ σ Csp Capp E Ceps cδ K η μ'' h
  obtain ⟨c5, hc5, hc⟩ := h.corHyp
  exact ⟨c5, hc5, corollary_main d α b L J X f₀ σ _ Csp Capp E Ceps cδ K η (μ'' / 2) 1 c5 hc⟩

end LargePrior
