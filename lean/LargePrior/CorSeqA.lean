import LargePrior.CorSpec

/-!
# Corollary 1: exponents, `log J_n`, and the `n ε̃_n²` identity (blueprint §B.1, B.2, B.4)
-/

open Filter Finset
open scoped Topology

noncomputable section

namespace LargePrior

/-- The hypotheses on the sequences used throughout the proof of Corollary 1:
`d ≥ 1`, `α_k > 0`, `b_k ≥ β_k`, sizes comparable, `C_sp, C_ε > 0`, `c_δ ∈ (0,1)`. -/
structure SeqHyp {d : ℕ} (α b : Fin d → ℝ) (L : ℕ → Fin d → ℕ) (J : ℕ → ℕ)
    (Csp Ceps cδ : ℝ) : Prop where
  hd : 0 < d
  hα : ∀ k, 0 < α k
  hb : ∀ k, betaExp α k ≤ b k
  hsize : SizesComparable b L J
  hCsp : 0 < Csp
  hCeps : 0 < Ceps
  hcδ : 0 < cδ
  hcδ1 : cδ < 1

/-- The sum `∑_k α_k⁻¹` is positive. -/
private lemma sum_inv_pos {d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k) :
    0 < ∑ k, (α k)⁻¹ :=
  Finset.sum_pos (fun k _ => inv_pos.mpr (hα k)) ⟨⟨0, hd⟩, Finset.mem_univ _⟩

private lemma alphaStar_pos {d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k) :
    0 < alphaStar α :=
  div_pos (by exact_mod_cast hd) (sum_inv_pos hd hα)

private lemma denom_pos {d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k) :
    0 < 2 * alphaStar α + d := by
  have h1 := alphaStar_pos hd hα
  have h2 : (0 : ℝ) < d := by exact_mod_cast hd
  linarith

/-- Positivity of the exponents: `α* > 0`, `r > 0`, `0 < D < 1`, `β_k > 0` (blueprint B.1). -/
lemma exponents_pos {d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k) :
    0 < alphaStar α ∧ 0 < rateExp α ∧ 0 < dimExp α ∧ dimExp α < 1 ∧ ∀ k, 0 < betaExp α k := by
  have ha := alphaStar_pos hd hα
  have hden := denom_pos hd hα
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  refine ⟨ha, div_pos ha hden, div_pos hdR hden, ?_, fun k => div_pos ha (mul_pos (hα k) hden)⟩
  rw [dimExp, div_lt_one hden]
  linarith

/-- Exponent identities (eq:aniso-identities): `α_k β_k = r`, `∑_k β_k = D`, `2r + D = 1`. -/
lemma exponent_identities {d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k) :
    (∀ k, α k * betaExp α k = rateExp α) ∧ ∑ k, betaExp α k = dimExp α ∧
      2 * rateExp α + dimExp α = 1 := by
  have hS := sum_inv_pos hd hα
  have hden := denom_pos hd hα
  refine ⟨fun k => ?_, ?_, ?_⟩
  · have hk := (hα k).ne'
    rw [betaExp, rateExp]
    field_simp
  · have hsum : ∑ k, betaExp α k = alphaStar α / (2 * alphaStar α + d) * ∑ k, (α k)⁻¹ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hk := (hα k).ne'
      rw [betaExp]
      field_simp
    have hprod : alphaStar α * ∑ k, (α k)⁻¹ = d := by
      rw [alphaStar, div_mul_cancel₀ _ hS.ne']
    rw [hsum, dimExp, ← hprod]
    ring
  · rw [rateExp, dimExp]
    field_simp

/-- `∏_k (c x^{b_k}) = c^d x^{∑_k b_k}` for `x > 0`. -/
private lemma prod_const_mul_rpow {d : ℕ} (b : Fin d → ℝ) (c x : ℝ) (hx : 0 < x) :
    ∏ k, (c * x ^ b k) = c ^ d * x ^ (∑ k, b k) := by
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Real.rpow_sum_of_pos hx]

/-- Two-sided power bounds on `J_n`: eventually `K₁ n^B ≤ J_n ≤ K₂ n^B` with `B = ∑_k b_k`. -/
private lemma J_bounds {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    ∃ K₁ K₂ : ℝ, 0 < K₁ ∧ 0 < K₂ ∧ ∀ᶠ n : ℕ in atTop,
      K₁ * (n : ℝ) ^ (∑ k, b k) ≤ J n ∧ (J n : ℝ) ≤ K₂ * (n : ℝ) ^ (∑ k, b k) := by
  obtain ⟨c, C, hc, hev⟩ := h.hsize
  have hCpos : 0 < C := by
    obtain ⟨n, hn, hn1⟩ := (hev.and (eventually_ge_atTop 1)).exists
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hp : 0 < (n : ℝ) ^ b ⟨0, h.hd⟩ := Real.rpow_pos_of_pos hnpos _
    have h1 := hn.1 ⟨0, h.hd⟩
    have hcp : 0 < c * (n : ℝ) ^ b ⟨0, h.hd⟩ := mul_pos hc hp
    by_contra hC
    have : C * (n : ℝ) ^ b ⟨0, h.hd⟩ ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (not_lt.mp hC) hp.le
    linarith [h1.1, h1.2]
  refine ⟨c ^ (d + 1), C ^ (d + 1), pow_pos hc _, pow_pos hCpos _, ?_⟩
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  obtain ⟨hL, hJl, hJu⟩ := hn
  have hlow : ∏ k, (c * (n : ℝ) ^ b k) ≤ ∏ k, (L n k : ℝ) :=
    Finset.prod_le_prod₀ (fun k _ => (mul_pos hc (Real.rpow_pos_of_pos hnpos _)).le)
      (fun k _ => (hL k).1)
  have hup : ∏ k, (L n k : ℝ) ≤ ∏ k, (C * (n : ℝ) ^ b k) :=
    Finset.prod_le_prod₀ (fun k _ => Nat.cast_nonneg _) (fun k _ => (hL k).2)
  rw [prod_const_mul_rpow b c _ hnpos] at hlow
  rw [prod_const_mul_rpow b C _ hnpos] at hup
  constructor
  · calc c ^ (d + 1) * (n : ℝ) ^ (∑ k, b k) = c * (c ^ d * (n : ℝ) ^ (∑ k, b k)) := by ring
      _ ≤ c * ∏ k, (L n k : ℝ) := mul_le_mul_of_nonneg_left hlow hc.le
      _ ≤ J n := hJl
  · calc (J n : ℝ) ≤ C * ∏ k, (L n k : ℝ) := hJu
      _ ≤ C * (C ^ d * (n : ℝ) ^ (∑ k, b k)) := mul_le_mul_of_nonneg_left hup hCpos.le
      _ = C ^ (d + 1) * (n : ℝ) ^ (∑ k, b k) := by ring

/-- `J_n → ∞` and `log J_n ≍ log n` (blueprint B.2). -/
lemma logJ_comparable {d : ℕ} {α b : Fin d → ℝ} {L : ℕ → Fin d → ℕ} {J : ℕ → ℕ}
    {Csp Ceps cδ : ℝ} (h : SeqHyp α b L J Csp Ceps cδ) :
    Tendsto J atTop atTop ∧ ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c * Real.log n ≤ Real.log (J n) ∧ Real.log (J n) ≤ C * Real.log n := by
  obtain ⟨K₁, K₂, hK₁, hK₂, hev⟩ := J_bounds h
  set B := ∑ k, b k with hB
  have hBpos : 0 < B := by
    have hD := (exponents_pos h.hd h.hα).2.2.1
    have hsum := (exponent_identities h.hd h.hα).2.1
    have : ∑ k, betaExp α k ≤ B := Finset.sum_le_sum fun k _ => h.hb k
    linarith
  have hlogn : Tendsto (fun n : ℕ => Real.log n) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  refine ⟨?_, B / 2, 2 * B, half_pos hBpos, ?_⟩
  · have hpow : Tendsto (fun n : ℕ => (n : ℝ) ^ B) atTop atTop :=
      (tendsto_rpow_atTop hBpos).comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun n : ℕ => K₁ * (n : ℝ) ^ B) atTop atTop := hpow.const_mul_atTop hK₁
    have h3 : Tendsto (fun n : ℕ => (J n : ℝ)) atTop atTop :=
      tendsto_atTop_mono' atTop (hev.mono fun n hn => hn.1) h2
    exact tendsto_natCast_atTop_iff.mp h3
  · filter_upwards [hev, eventually_ge_atTop 1,
      hlogn.eventually_ge_atTop (-Real.log K₁ / (B / 2)),
      hlogn.eventually_ge_atTop (Real.log K₂ / B)] with n hn hn1 hl1 hl2
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have hpow : 0 < (n : ℝ) ^ B := Real.rpow_pos_of_pos hnpos B
    have hlogpow : Real.log ((n : ℝ) ^ B) = B * Real.log n := Real.log_rpow hnpos B
    have hlow : Real.log K₁ + B * Real.log n ≤ Real.log (J n) := by
      rw [← hlogpow, ← Real.log_mul hK₁.ne' hpow.ne']
      exact Real.log_le_log (mul_pos hK₁ hpow) hn.1
    have hup : Real.log (J n) ≤ Real.log K₂ + B * Real.log n := by
      rw [← hlogpow, ← Real.log_mul hK₂.ne' hpow.ne']
      exact Real.log_le_log (lt_of_lt_of_le (mul_pos hK₁ hpow) hn.1) hn.2
    have h1 := (div_le_iff₀ (half_pos hBpos)).mp hl1
    have h2 := (div_le_iff₀ hBpos).mp hl2
    constructor <;> nlinarith

/-- `n ε̃_n² = C_ε² N_n^D log J_n` whenever `n > 0` and `J_n > 1` (blueprint B.4). -/
lemma n_epsT_sq_eq {d : ℕ} {α : Fin d → ℝ} (hd : 0 < d) (hα : ∀ k, 0 < α k) (Ceps : ℝ)
    {n J : ℕ} (hn : 0 < n) (hJ : 1 < J) :
    (n : ℝ) * corEpsT Ceps α n J ^ 2 = Ceps ^ 2 * corN n J ^ dimExp α * Real.log J := by
  have hlog : 0 < Real.log J := Real.log_pos (by exact_mod_cast hJ)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hN : 0 < corN n J := div_pos hnR hlog
  have hnN : (n : ℝ) = corN n J * Real.log J := by
    rw [corN]
    field_simp
  have hD : dimExp α = 1 + -2 * rateExp α := by
    have := (exponent_identities hd hα).2.2
    linarith
  have hsq : (corN n J ^ (-rateExp α)) ^ 2 = corN n J ^ (-2 * rateExp α) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN.le]
    ring_nf
  have hND : corN n J * corN n J ^ (-2 * rateExp α) = corN n J ^ dimExp α := by
    rw [hD, Real.rpow_add hN, Real.rpow_one]
  rw [corEpsT, mul_pow, hsq, hnN, ← hND]
  ring

end LargePrior
