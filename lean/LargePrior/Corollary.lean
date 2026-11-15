import LargePrior.CorSeq
import LargePrior.Asymptotic
import LargePrior.WG4Perm

/-!
# Corollary 1, abstract form (blueprint §B.5–B.6)

Assumption 2 from the profile at the balanced budget, and the corollary from Theorem 1.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

/-- Each term `m_{n,k}^{-α_k}` is at most `N_n^{-r}`. -/
private lemma corM_rpow_le {n J d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k)
    (hN : 1 ≤ corN n J) (k : Fin d) :
    (corM α n J k : ℝ) ^ (-α k) ≤ corN n J ^ (-rateExp α) := by
  have hN0 : 0 < corN n J := lt_of_lt_of_le one_pos hN
  have hpos : 0 < corN n J ^ betaExp α k := Real.rpow_pos_of_pos hN0 _
  have hge : corN n J ^ betaExp α k ≤ (corM α n J k : ℝ) := Nat.le_ceil _
  have h1 := Real.rpow_le_rpow_of_nonpos hpos hge (neg_nonpos.2 (hα k).le)
  have h2 : (corN n J ^ betaExp α k) ^ (-α k) = corN n J ^ (-rateExp α) := by
    rw [← Real.rpow_mul hN0.le]
    congr 1
    obtain ⟨hαβ, -, -⟩ := exponent_identities hd hα
    linarith [hαβ k]
  rwa [h2] at h1

/-- **Assumption 2 from the profile** (blueprint B.5, Step 2): at a fixed `n` with `N_n ≥ 1`,
`1 ≤ m_{n,k} ≤ L_k`, and `a_n ≤ J`, the profile vector at the balanced budget `m_n`, with an
active set of exactly `a_n` indices containing its support, satisfies Assumption 2 with
`ε̃_n = corEpsT`, `δ_n = corDelta`, `E_n = E`, `a_n = corA`, provided `C_ε ≥ d C_app`. -/
lemma sparseApprox_of_profile {n J d : ℕ} {X : Matrix (Fin n) (Fin J) ℝ} {f₀ : Fin n → ℝ}
    {L : Fin d → ℕ} {α : Fin d → ℝ} {Csp Capp E Ceps cδ : ℝ}
    (hd : 0 < d) (hα : ∀ k, 0 < α k) (hCapp : 0 ≤ Capp) (hCepsApp : (d : ℝ) * Capp ≤ Ceps)
    (hcδ : 0 ≤ cδ) (hprof : ProfileAt X f₀ L α Csp Capp E) (hN : 1 ≤ corN n J)
    (hm : ∀ k, 1 ≤ corM α n J k ∧ corM α n J k ≤ L k) (haJ : corA Csp α n J ≤ J) :
    ∃ θ₀ S, SparseApprox X f₀ (corEpsT Ceps α n J) (corDelta cδ Ceps α n J) E
      (corA Csp α n J) θ₀ S := by
  obtain ⟨θ₀, hsupp, herr, hE⟩ := hprof (corM α n J) hm
  have hN0 : 0 < corN n J := lt_of_lt_of_le one_pos hN
  have hNr : 0 ≤ corN n J ^ (-rateExp α) := Real.rpow_nonneg hN0.le _
  -- support size
  have hsc : suppCard θ₀ ≤ corA Csp α n J := by
    have h1 : (suppCard θ₀ : ℝ) ≤ (corA Csp α n J : ℝ) :=
      hsupp.trans (Nat.le_ceil _)
    exact_mod_cast h1
  -- the active set
  obtain ⟨S, hS, hScard⟩ : ∃ S : Finset (Fin J), (univ.filter fun j => θ₀ j ≠ 0) ⊆ S ∧
      S.card = corA Csp α n J := by
    obtain ⟨u, hu1, -, hu3⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ _)
      (show (univ.filter fun j => θ₀ j ≠ 0).card ≤ corA Csp α n J from hsc)
      (show corA Csp α n J ≤ (univ : Finset (Fin J)).card by simpa using haJ)
    exact ⟨u, hu1, hu3⟩
  -- δ ≥ 0
  have hεt : 0 ≤ corEpsT Ceps α n J := by
    have : 0 ≤ Ceps := le_trans (mul_nonneg (Nat.cast_nonneg _) hCapp) hCepsApp
    exact mul_nonneg this hNr
  have hδ : 0 ≤ corDelta cδ Ceps α n J :=
    div_nonneg (mul_nonneg hcδ hεt) (Nat.cast_nonneg _)
  refine ⟨θ₀, S, ?_, ?_, hE, hScard, ?_⟩
  · refine herr.trans ?_
    calc Capp * ∑ k, (corM α n J k : ℝ) ^ (-α k)
        ≤ Capp * ∑ _k : Fin d, corN n J ^ (-rateExp α) :=
          mul_le_mul_of_nonneg_left
            (Finset.sum_le_sum fun k _ => corM_rpow_le hd hα hN k) hCapp
      _ = ((d : ℝ) * Capp) * corN n J ^ (-rateExp α) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
      _ ≤ Ceps * corN n J ^ (-rateExp α) := mul_le_mul_of_nonneg_right hCepsApp hNr
  · refine le_trans ?_ hsc
    unfold numLarge suppCard
    apply Finset.card_le_card
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    intro h0
    rw [h0, abs_zero] at hj
    linarith
  · intro j hj
    have : θ₀ j = 0 := by
      by_contra h0
      exact hj (hS (by simpa using h0))
    rw [this, abs_zero]
    exact hδ

/-- From `CorHyp`, the sequence hypotheses. -/
lemma CorHyp.seqHyp {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ} {f₀ : ∀ n : ℕ, Fin n → ℝ} {σ : ℝ}
    {pdf : ℕ → ℝ → ℝ} {Csp Capp E Ceps cδ K η μ c4 c5 : ℝ}
    (h : CorHyp α b L J X f₀ σ pdf Csp Capp E Ceps cδ K η μ c4 c5) :
    SeqHyp α b L J Csp Ceps cδ :=
  ⟨h.hd, h.hα, h.hb, h.hsize, h.hCsp, h.hCeps, h.hcδ, h.hcδ1⟩

/-- Theorem 1's hypotheses hold for the corollary's sequences, for any `M_n → ∞`. -/
lemma CorHyp.asymptoticHyp {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ} {f₀ : ∀ n : ℕ, Fin n → ℝ} {σ : ℝ}
    {pdf : ℕ → ℝ → ℝ} {Csp Capp E Ceps cδ K η μ c4 c5 : ℝ}
    (h : CorHyp α b L J X f₀ σ pdf Csp Capp E Ceps cδ K η μ c4 c5) {M : ℕ → ℝ}
    (hM : Tendsto M atTop atTop) :
    AsymptoticHyp J X f₀ σ pdf (fun n => corEpsT Ceps α n (J n))
      (fun n => corDelta cδ Ceps α n (J n)) (fun _ => E) M (fun n => corA Csp α n (J n))
      K η μ c4 c5 := by
  have hs := h.seqHyp
  have hev := seq_eventually hs
  obtain ⟨hJtop, -⟩ := logJ_comparable hs
  refine
    { hσ := h.hσ, hK := h.hK, hη := h.hη, hη1 := h.hη1, hμ := h.hμ, hc4 := h.hc4, hc5 := h.hc5
      hJ := hJtop, hnεt := tendsto_n_epsT_sq hs, hs := tendsto_sRate_log hs
      hM := hM, hpdf := h.hpdf
      hεt := hev.mono fun _ ⟨_, _, _, _, _, hεt, _, _⟩ => hεt
      hδ := hev.mono fun _ ⟨_, _, _, _, _, _, hδ, _⟩ => hδ
      hE := Eventually.of_forall fun _ => h.hE
      ha := hev.mono fun _ ⟨_, _, _, ha, haJ, _, _, _⟩ => ⟨ha, haJ⟩
      hδεt := hev.mono fun _ ⟨_, _, _, _, _, _, _, hδεt⟩ => hδεt
      hbasis := h.hbasis, hA2 := ?_, h3 := h.h3, h5 := h.h5 }
  filter_upwards [hev, h.hprofile, h.h4] with n hn hprof h4n
  obtain ⟨_, hN, hm, _, haJ, _, _, _⟩ := hn
  obtain ⟨θ₀, S, hA⟩ := sparseApprox_of_profile h.hd h.hα h.hCapp h.hCepsApp h.hcδ.le hprof
    hN hm haJ
  -- (WG4) is assumed for one set `S₀` of size `a_n`; transfer it to the active set `S`.
  obtain ⟨S₀, hS₀, hW⟩ := h4n
  obtain ⟨happrox, hlarge, hbound, hScard, hoff⟩ := hA
  exact ⟨θ₀, S, ⟨happrox, hlarge, hbound, hScard, hoff⟩,
    wg4_of_card_eq (hS₀.trans hScard.symm) hW⟩

/-- **Corollary 1, first sentence**: Assumption 2 and the standing requirements hold for the
corollary's sequences, so that Theorem 1 applies, for every `M_n → ∞`. -/
theorem cor_asymptoticHyp : CorTheorem1InputsStatement :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h _ hM => h.asymptoticHyp hM

/-- `farSet` is antitone in the radius. -/
lemma farSet_anti {n J : ℕ} (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) {r₁ r₂ : ℝ}
    (h : r₁ ≤ r₂) : farSet X f₀ r₂ ⊆ farSet X f₀ r₁ :=
  fun _ hθ => lt_of_le_of_lt h hθ

/-- `{#large > t} ⊆ {#large > m}` when `m ≤ t` (real threshold against a natural one). -/
lemma denseSetReal_subset_denseSet {J : ℕ} (δ : ℝ) {t : ℝ} {m : ℕ} (h : (m : ℝ) ≤ t) :
    denseSetReal (J := J) δ t ⊆ denseSet δ m := fun θ hθ => by
  have hlt : (m : ℝ) < numLarge δ θ := lt_of_le_of_lt h hθ
  exact_mod_cast hlt

/-- Monotonicity of `denseSet` in the count. -/
lemma denseSet_anti {J : ℕ} (δ : ℝ) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    denseSet (J := J) δ m₂ ⊆ denseSet δ m₁ :=
  fun _ hθ => lt_of_le_of_lt h hθ

/-- **Corollary 1** (abstract form). -/
theorem corollary_main : CorollaryStatement := by
  intro d α b L J X f₀ σ pdf Csp Capp E Ceps cδ K η μ c4 c5 h
  refine ⟨fun M hM => h.asymptoticHyp hM, ?_⟩
  have hs := h.seqHyp
  set A : ℕ := Aconst K η σ μ c4 c5 with hAdef
  have hA1 : 1 ≤ A := one_le_Aconst h.hμ (C1_nonneg h.hK.le h.hη.le h.hσ h.hc4 h.hc5)
  -- (i): the orders, with one constant `C`
  obtain ⟨C, hC, hord⟩ := cor_orders hs
  refine ⟨⟨C, hC, hord⟩, corAprime_pos hA1 h.hCsp, corExpConst_pos h.hCsp h.hCeps,
    fun M hM => ?_⟩
  -- Theorem 1 applied once, with the same `M_n`
  obtain ⟨hmain, hfar, hdense⟩ := asymptotic_theorem _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (h.asymptoticHyp hM)
  -- Translation 3 (the support size): `A s_n ≤ A' a_n`
  have hdensesub : ∀ᶠ n in atTop,
      denseSetReal (J := J n) (corDelta cδ Ceps α n (J n))
          (corAprime A d Csp Ceps * corA Csp α n (J n)) ⊆
        denseSet (corDelta cδ Ceps α n (J n))
          (A * sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n))) := by
    filter_upwards [cor_sRate_le_Aprime hs A] with n hn
    exact denseSetReal_subset_denseSet _ hn
  -- Translation 2 (the exponent): `e^{-n ε̃_n²} ≤ e^{-c n ε_n²}`
  have hexple : ∀ᶠ n : ℕ in atTop, ∀ k : ℝ, 0 ≤ k →
      ENNReal.ofReal (k * Real.exp (-((n : ℝ) * corEpsT Ceps α n (J n) ^ 2))) ≤
        ENNReal.ofReal (k * Real.exp (-(corExpConst d Csp Ceps *
          ((n : ℝ) * epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ^ 2)))) := by
    filter_upwards [cor_exp_lower_explicit hs] with n hn k hk
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ hk
    exact Real.exp_le_exp.2 (neg_le_neg hn)
  refine ⟨?_, hfar, ?_⟩
  · filter_upwards [hmain, hdensesub, hexple] with n hn hd' he
    obtain ⟨hfarBound, hdenseBound⟩ := hn
    refine ⟨?_, ?_⟩
    · exact hfarBound.trans (he 5 (by norm_num))
    · exact le_trans (lintegral_mono fun y => measure_mono hd')
        (hdenseBound.trans (he 2 (by norm_num)))
  · -- convergence in probability, support size
    intro ζ hζ
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds (hdense ζ hζ)
      (Eventually.of_forall fun n => bot_le) ?_
    filter_upwards [hdensesub] with n hn
    exact measure_mono fun y hy => lt_of_lt_of_le hy (measure_mono hn)

end LargePrior
