import LargePrior.ChebProfile
import LargePrior.ChebTransfer
import LargePrior.CorHorseshoe
import LargePrior.Jackson

/-!
# Corollary 1 for the tensor Chebyshev dictionary with the horseshoe prior

Assembles the Chebyshev end-to-end instances of Corollary 1:
* `cheb_sizes`: canonical sizes `chebL b n k = ⌈n^{b k}⌉` and `chebJ b n = ∏_k chebL b n k`
  satisfy `SizesComparable b (chebL b) (chebJ b)`;
* `cor_cheb_explicit_of`: explicit-constant Corollary 1 (`C_sp = 1`, `E = R`, `C_ε ≥ d C_app`)
  from per-coordinate transfer and Jackson premises;
* `cor_chebyshev_of` / `cor_chebyshev_ex_of`: general-`α` corollaries conditional on
  `ChebTransferStatement`;
* `cor_chebyshev_holder`: unconditional Corollary 1 for `α ∈ (0, 1)^d`, combining
  `cheb_transfer_le_one` with `jackson_lip`.
-/

open MeasureTheory Filter Finset
open scoped Topology Matrix

noncomputable section

namespace LargePrior

/-! ## Canonical Chebyshev dictionary sizes -/

/-- Canonical Chebyshev sizes: `L_{n,k} = ⌈n^{b_k}⌉ ≍ n^{b_k}` and `J_n = ∏_k L_{n,k}` exactly
(tensor cardinality). The comparison constants are `1` and `2`, valid for every `n ≥ 1`. -/
lemma cheb_sizes {d : ℕ} {b : Fin d → ℝ} (hb : ∀ k, 0 < b k) :
    SizesComparable b (chebL b) (chebJ b) := by
  refine ⟨1, 2, one_pos, ?_⟩
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hL : ∀ k, 1 * (n : ℝ) ^ b k ≤ chebL b n k ∧ (chebL b n k : ℝ) ≤ 2 * (n : ℝ) ^ b k := by
    intro k
    have h1 : 1 ≤ (n : ℝ) ^ b k := Real.one_le_rpow (by exact_mod_cast hn) (hb k).le
    have h2 : (n : ℝ) ^ b k ≤ chebL b n k := Nat.le_ceil _
    have h3 : (chebL b n k : ℝ) < (n : ℝ) ^ b k + 1 := Nat.ceil_lt_add_one (by linarith)
    constructor <;> linarith
  have hJ : (chebJ b n : ℝ) = ∏ k, (chebL b n k : ℝ) := by
    simp only [chebJ, Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
  have hP : 0 ≤ ∏ k, (chebL b n k : ℝ) := Finset.prod_nonneg fun k _ => Nat.cast_nonneg _
  refine ⟨hL, ?_, ?_⟩
  · rw [hJ]; linarith
  · rw [hJ]; linarith

/-! ## Core explicit-constant Corollary 1 -/

/-- Core explicit-constant Corollary 1 for the tensor Chebyshev dictionary with the horseshoe prior,
taking per-coordinate smoothness-transfer and Jackson hypotheses. -/
lemma cor_cheb_explicit_of {d : ℕ} {hd : 0 < d} {α : Fin d → ℝ} {r : Fin d → ℕ}
    {CJ : Fin d → ℝ} (hT : ∀ k (r' : ℕ), α k < r' → ChebTransferPremise (α k) r')
    (hJ : ∀ k, JacksonIneq (α k) (r k) (CJ k)) :
    CorChebExplicit d hd α r CJ := by
  intro R Ceps hCeps b J L e f₀ x σ η μ'' cδ h hsize hcδ hcδ1
  exact cor_horseshoe d α b L J (chebXe e x) (fun n i => f₀ (x n i)) σ 1
    (chebCapp hd α r CJ R) R Ceps cδ (Real.sqrt 2 ^ d) η μ''
    { hd := hd
      hα := h.hα
      hb := h.hb
      hsize := hsize
      hσ := h.hσ
      hK := by positivity
      hbasis := Eventually.of_forall fun n =>
        chebyshev_basis n (J n) d (fun j k => ((e n j) k : ℕ)) (x n) (h.hx n)
      hCsp := one_pos
      hCapp := chebCapp_nonneg hd h.hR.le
      hE := h.hR
      hprofile := Eventually.of_forall fun n =>
        chebyshev_profile_at_core hd hT h.hα h.hr hJ h.hR.le h.hball (h.hx n)
      hCeps := lt_of_lt_of_le (mul_pos (by exact_mod_cast hd) (chebCapp_pos hd h.hR)) hCeps
      hCepsApp := hCeps
      hcδ := hcδ
      hcδ1 := hcδ1
      hη := h.hη
      hη1 := h.hη1
      hμ'' := h.hμ'' }

/-! ## Conditional general-`α` corollaries -/

/-- **Corollary 1, tensor Chebyshev dictionary, explicit constants**, conditional on
`ChebTransferStatement`. -/
theorem cor_chebyshev_of (hT : ChebTransferStatement) : CorChebyshevStatement := by
  intro d hd α r CJ hJ R Ceps hCeps b J L e f₀ x σ η μ'' cδ h hsize hcδ hcδ1
  exact cor_cheb_explicit_of (fun k r' hr' => hT (α k) r' (h.hα k) hr') hJ
    R Ceps hCeps b J L e f₀ x σ η μ'' cδ h hsize hcδ hcδ1

/-- **Corollary 1, tensor Chebyshev dictionary, existential-constant shape**, conditional on
`ChebTransferStatement`. -/
theorem cor_chebyshev_ex_of (hT : ChebTransferStatement) : CorChebyshevExStatement := by
  intro d α r CJ R hd hJ _hα _hr hR
  refine ⟨1, (d : ℝ) * chebCapp hd α r CJ R, R, one_pos,
    mul_pos (by exact_mod_cast hd) (chebCapp_pos hd hR), hR, ?_⟩
  intro b f₀ x σ η μ'' cδ h hcδ hcδ1
  have hbpos : ∀ k, 0 < b k := fun k =>
    lt_of_lt_of_le ((exponents_pos hd h.hα).2.2.2.2 k) (h.hb k)
  exact cor_chebyshev_of hT d hd α r CJ hJ R ((d : ℝ) * chebCapp hd α r CJ R) le_rfl b
    (chebJ b) (chebL b) (fun n => (Fintype.equivFin (ChebIdx (chebL b n))).symm) f₀ x
    σ η μ'' cδ h (cheb_sizes hbpos) hcδ hcδ1

/-! ## Unconditional Corollary 1 for `α ∈ (0, 1)^d` (MS1) -/

/-- **Corollary 1, tensor Chebyshev dictionary, `α ∈ (0, 1)^d`, with no assumed classical input**:
combines `cheb_transfer_le_one` with `jackson_lip` at `r = 1`. -/
theorem cor_chebyshev_holder : CorChebyshevHolderStatement := by
  intro d hd α hα hα1
  choose CJ hJ using fun k => jackson_lip (hα k) (hα1 k)
  exact ⟨CJ, hJ,
    cor_cheb_explicit_of (fun k _ hr' => cheb_transfer_le_one (hα k) (hα1 k).le hr') hJ⟩

end LargePrior
