import LargePrior.CorSpec

/-!
# LargePrior: specification of the Chebyshev dictionary (L-02, frozen at gate G0)

Definitions and statements (as `Prop`s) for the Chebyshev part of Corollary 1 of the paper:
the dictionary (App. D, D:475–500), the univariate Hölder class `C^α([0,1])` and the transfer
constant `C_tr(α)` (D:502–512), Lemma `chebyshev-profile` (D:514–531), the tensor-product
dictionary and the sectional class `C^α_sec([0,1]^d; R)` (D:580–599), Lemma
`chebyshev-aniso-profile` (D:601–622), and the end-to-end Corollary 1 for this dictionary with the
horseshoe prior (S:143–204).

This file contains definitions only. Proofs live in `ChebBasis`, `ChebTransfer`,
`ChebTransferHigh`, `ChebTensor`, `ChebProfile`, `ChebEndToEnd`, `ChebMain` and `ChebChecks`.

Conventions fixed here (see `L02/PLAN.md` §1.1 and HQ rulings H3, H4, P1):
* the radius is `R ≥ 0` in the lemmas and `R > 0` in the corollaries;
* the sectional class contains `ContinuousOn f₀ (unitCube d)` (H3);
* the difference order `r` of the Hölder–Zygmund norm is an explicit argument, always with
  `α < r` (D:196, D:512); the side condition guards the error and transfer bounds;
* the coefficient map is chosen before the dictionary size `L`, which expresses "the nonzero
  entries do not depend on `J`" (D:526, D:617), and before `r` and the Jackson constant, which
  the construction does not use (D:526, D:556–570, D:617, D:661–667).
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

/-! ## The fold and the Chebyshev dictionary (D:475–498) -/

/-- The fold `x(u) = (1 + cos 2πu)/2` (eq:cheb-fold), a smooth, even, 1-periodic map of `ℝ`
onto `[0,1]`. -/
def chebFold (u : ℝ) : ℝ := (1 + Real.cos (2 * Real.pi * u)) / 2

/-- The univariate Chebyshev atom on `[0,1]`: `φ₀ = 1` and `φ_j(x) = √2 T_j(2x − 1)` for `j ≥ 1`
(D:477–481). -/
def chebAtom (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then 1 else Real.sqrt 2 * (Polynomial.Chebyshev.T ℝ (j : ℤ)).eval (2 * x - 1)

/-- `f_ϑ = Σ_{j<L} ϑ_j φ_j`, the univariate Chebyshev series of the dictionary `C_L` with
coefficients read off a coefficient map `ϑ : ℕ → ℝ`. -/
def chebSum (ϑ : ℕ → ℝ) (L : ℕ) (x : ℝ) : ℝ := ∑ j ∈ range L, ϑ j * chebAtom j x

/-- Index set of the tensor Chebyshev dictionary `C_L`: `0 ≤ j_k ≤ L_k − 1` (D:577–581). -/
abbrev ChebIdx {d : ℕ} (L : Fin d → ℕ) := (k : Fin d) → Fin (L k)

/-- Tensor Chebyshev atom on `[0,1]^d`: `Φ_j(x) = ∏_k φ_{j_k}(x_k)`. -/
def chebTensor {d : ℕ} (j : Fin d → ℕ) (x : Fin d → ℝ) : ℝ := ∏ k, chebAtom (j k) (x k)

/-- `f_θ = Σ_j θ_j Φ_j` over the tensor Chebyshev dictionary `C_L`. -/
def chebSeries {d : ℕ} {L : Fin d → ℕ} (θ : ChebIdx L → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ j, θ j * chebTensor (fun k => (j k : ℕ)) x

/-! ## The univariate class `C^α([0,1])` and the transfer constant (D:500–512) -/

/-- `s = ⌈α⌉ − 1`, the number of derivatives in `C^α` (Lipschitz–Hölder convention at
integers). -/
def chebS (α : ℝ) : ℕ := ⌈α⌉₊ - 1

/-- `β = α − s ∈ (0,1]` for `α > 0`. -/
def chebBeta (α : ℝ) : ℝ := α - chebS α

/-- Ball of radius `R` of `C^α([0,1])` (D:502–503, with one radius for all the bounds as at
D:60–68): `f` is `s` times continuously differentiable on `[0,1]`, with one-sided derivatives at the
endpoints; `|f^{(j)}| ≤ R` on `[0,1]` for `0 ≤ j ≤ s`; and
`|f^{(s)}(y) − f^{(s)}(z)| ≤ R |y − z|^β` on `[0,1]`. -/
def HolderBallIcc (α R : ℝ) (f : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ (chebS α) f (Set.Icc 0 1) ∧
    (∀ j ≤ chebS α, ∀ y ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin j f (Set.Icc 0 1) y| ≤ R) ∧
    ∀ y ∈ Set.Icc (0 : ℝ) 1, ∀ z ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDerivWithin (chebS α) f (Set.Icc 0 1) y -
          iteratedDerivWithin (chebS α) f (Set.Icc 0 1) z| ≤ R * |y - z| ^ chebBeta α

/-- `κ_{0,β} = 1` and `κ_{s,β} = Σ_{k=1}^{s} (1 + 2k^β) 2^{−k} S(s,k)` for `s ≥ 1`, with `S(s,k)`
the Stirling numbers of the second kind (eq:cheb-Ctr). -/
def chebKappa (s : ℕ) (β : ℝ) : ℝ :=
  if s = 0 then 1
  else ∑ k ∈ Icc 1 s, (1 + 2 * (k : ℝ) ^ β) * ((2 : ℝ) ^ k)⁻¹ * (Nat.stirlingSecond s k : ℝ)

/-- The transfer constant `C_tr(α) = 1 + 2^{r − s − 1} π^β (2π)^s κ_{s,β}` (eq:cheb-Ctr), for the
difference order `r > α` of the Hölder–Zygmund norm (so `r − s − 1 ≥ 0`). -/
def chebCtr (α : ℝ) (r : ℕ) : ℝ :=
  1 + (2 : ℝ) ^ (r - chebS α - 1) * Real.pi ^ chebBeta α * (2 * Real.pi) ^ chebS α *
    chebKappa (chebS α) (chebBeta α)

/-- The smoothness transfer (eq:cheb-transfer) at fixed `(α, r)`: for every `f` in the ball of
radius `R` of `C^α([0,1])`, the folded function `f ∘ x` lies in the periodic Hölder–Zygmund ball
of radius `C_tr(α) R`. Lane B works against this premise; `ChebTransferStatement` is the theorem. -/
def ChebTransferPremise (α : ℝ) (r : ℕ) : Prop :=
  ∀ (R : ℝ) (f : ℝ → ℝ), HolderBallIcc α R f → HZBall1 α r (chebCtr α r * R) (f ∘ chebFold)

/-- **The smoothness transfer** (first part of the proof of Lemma chebyshev-profile,
D:536–553), for every `0 < α < r`. -/
def ChebTransferStatement : Prop :=
  ∀ (α : ℝ) (r : ℕ), 0 < α → α < r → ChebTransferPremise α r

/-! ## The sectional class (D:594–599) -/

/-- The sectional class `C^α_sec([0,1]^d; R)` (D:594–599): `f₀` continuous on the cube (H3), and
for every point `x` of the cube (faces included) and every direction `k`, the section of `f₀`
through `x` in direction `k` lies in the ball of radius `R` of `C^{α_k}([0,1])`. -/
def SecHolderBall {d : ℕ} (α : Fin d → ℝ) (R : ℝ) (f₀ : (Fin d → ℝ) → ℝ) : Prop :=
  ContinuousOn f₀ (unitCube d) ∧
    ∀ x ∈ unitCube d, ∀ k : Fin d, HolderBallIcc (α k) R (sectionAt f₀ x k)

/-! ## Profile constants (D:526, D:610–614) -/

/-- The univariate profile constant `C = max{2, 4·3^α C_α C_tr(α)}` (eq:chebyshev-profile). -/
def chebC (α : ℝ) (r : ℕ) (CJ : ℝ) : ℝ := max 2 (4 * 3 ^ α * CJ * chebCtr α r)

/-- `c_k = R max{2, 4·3^{α_k} C_{α_k} C_tr(α_k)}` (D:612–615). -/
def chebCk (α : ℝ) (r : ℕ) (CJ R : ℝ) : ℝ := R * chebC α r CJ

/-- `C_app = 3^{d−1} max_k c_k` (eq:chebyshev-aniso-profile), for `d ≥ 1`. -/
def chebCapp {d : ℕ} (hd : 0 < d) (α : Fin d → ℝ) (r : Fin d → ℕ) (CJ : Fin d → ℝ) (R : ℝ) : ℝ :=
  3 ^ (d - 1) * (univ : Finset (Fin d)).sup' ⟨⟨0, hd⟩, mem_univ _⟩
    (fun k => chebCk (α k) (r k) (CJ k) R)

/-! ## Dictionary sizes and design matrices -/

/-- Design matrix of the tensor Chebyshev dictionary `C_L` at a design `x`, for an arbitrary
enumeration `e : Fin J ≃ C_L` of its atoms ("any fixed enumeration of the atoms may serve as the
indexing", D:587). It is the paper's dictionary when every `L k ≥ 1`; if some `L k = 0` the index
set is empty and `ProfileAt` has no admissible rectangle. -/
def chebDesign {d n J : ℕ} {L : Fin d → ℕ} (e : Fin J ≃ ChebIdx L) (x : Fin n → Fin d → ℝ) :
    Matrix (Fin n) (Fin J) ℝ :=
  designMatrix (fun j => chebTensor (fun k => ((e j) k : ℕ))) x

/-- The sequence of design matrices for sizes `L_n`, totals `J_n` and enumerations
`e_n : Fin J_n ≃ C_{L_n}` (S:160). -/
def chebXe {d : ℕ} {J : ℕ → ℕ} {L : ℕ → Fin d → ℕ} (e : ∀ n, Fin (J n) ≃ ChebIdx (L n))
    (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (n : ℕ) : Matrix (Fin n) (Fin (J n)) ℝ :=
  chebDesign (e n) (x n)

/-- Chebyshev dictionary size in coordinate `k` at sample size `n`: `L_{n,k} = ⌈n^{b_k}⌉`
(the canonical choice, mirroring `fourierM`). -/
def chebL {d : ℕ} (b : Fin d → ℝ) (n : ℕ) (k : Fin d) : ℕ := ⌈(n : ℝ) ^ b k⌉₊

/-- Total size `J_n = ∏_k L_{n,k}` of the tensor Chebyshev dictionary. -/
def chebJ {d : ℕ} (b : Fin d → ℝ) (n : ℕ) : ℕ := Fintype.card (ChebIdx (chebL b n))

/-- Design matrix of the tensor Chebyshev dictionary at the design `x n` (columns enumerated by
a fixed bijection `Fin J_n ≃` index set). -/
def chebX {d : ℕ} (b : Fin d → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin (chebJ b n)) ℝ :=
  chebXe (fun n => (Fintype.equivFin (ChebIdx (chebL b n))).symm) x n

/-! ## Statements -/

/-- **Assumption 1 for every tensor Chebyshev dictionary** (D:528, D:619): any finite family of
tensor atoms and any design in `[0,1]^d` give `BasisBound` with `K = 2^{d/2}`. -/
def ChebyshevBasisStatement : Prop :=
  ∀ (n J d : ℕ) (idx : Fin J → Fin d → ℕ) (x : Fin n → Fin d → ℝ),
    (∀ i, x i ∈ unitCube d) →
    BasisBound (designMatrix (fun j => chebTensor (idx j)) x) (Real.sqrt 2 ^ d)

/-- **Lemma chebyshev-profile** (D:514–531), sup-norm form with the displayed constant. For
`α > 0`, `R ≥ 0`, `f` in the ball of radius `R` of `C^α([0,1])` and `m ≥ 1`, there is a
coefficient map `ϑ`, chosen before the dictionary size and before the difference order and the
Jackson constant (the construction of D:556–570 uses neither), with support in `{0, …, m − 1}` and
`|ϑ_j| ≤ R`, such that for every order `r > α`, every Jackson constant `C_J` for `(α, r)` and every
dictionary size `L ≥ m`, `sup_{[0,1]} |f − Σ_{j<L} ϑ_j φ_j| ≤ max{2, 4·3^α C_J C_tr(α)} R m^{−α}`.
The empirical-norm form (D:526) follows by bounding `empNorm` by the uniform error, with the same
coefficient map; the actual-design interface is `ChebyshevProfileAtStatement` at `d = 1`. -/
def ChebyshevProfileStatement : Prop :=
  ∀ (α R : ℝ) (f : ℝ → ℝ) (m : ℕ),
    0 < α → 0 ≤ R → HolderBallIcc α R f → 1 ≤ m →
    ∃ ϑ : ℕ → ℝ, (∀ j, m ≤ j → ϑ j = 0) ∧ (∀ j, |ϑ j| ≤ R) ∧
      ∀ (r : ℕ) (CJ : ℝ), α < r → JacksonIneq α r CJ →
        ∀ L : ℕ, m ≤ L → ∀ x ∈ Set.Icc (0 : ℝ) 1,
          |f x - chebSum ϑ L x| ≤ chebC α r CJ * R * (m : ℝ) ^ (-α)

/-- **Lemma chebyshev-aniso-profile** (D:601–622), sup-norm form with the displayed constant.
For `d ≥ 1`, `α_k > 0`, `R ≥ 0`, `f₀` in `C^α_sec([0,1]^d; R)` and every rectangle `m` with
`m_k ≥ 1`, there is a coefficient map `ϑ`, chosen before the dictionary sizes and before the
difference orders and Jackson constants, supported in `∏_k {0, …, m_k − 1}`, with `|ϑ_j| ≤ R`, such
that for all orders `r_k > α_k`, all Jackson constants `C_k` for `(α_k, r_k)` and all sizes `L ≥ m`
(coordinatewise), `sup_{[0,1]^d} |f₀ − Σ_{j ∈ C_L} ϑ_j Φ_j| ≤ 3^{d−1} max_k c_k · Σ_k m_k^{−α_k}`.
The empirical-norm form (D:617) is `ChebyshevProfileAtStatement`. -/
def ChebyshevAnisoProfileStatement : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (α : Fin d → ℝ) (R : ℝ) (f₀ : (Fin d → ℝ) → ℝ) (m : Fin d → ℕ),
    (∀ k, 0 < α k) → 0 ≤ R → SecHolderBall α R f₀ → (∀ k, 1 ≤ m k) →
    ∃ ϑ : (Fin d → ℕ) → ℝ, (∀ j, (∃ k, m k ≤ j k) → ϑ j = 0) ∧ (∀ j, |ϑ j| ≤ R) ∧
      ∀ (r : Fin d → ℕ) (CJ : Fin d → ℝ), (∀ k, α k < r k) →
        (∀ k, JacksonIneq (α k) (r k) (CJ k)) →
        ∀ L : Fin d → ℕ, (∀ k, m k ≤ L k) → ∀ x ∈ unitCube d,
          |f₀ x - chebSeries (L := L) (fun j => ϑ (fun k => (j k : ℕ))) x| ≤
            chebCapp hd α r CJ R * ∑ k, (m k : ℝ) ^ (-α k)

/-- **The empirical profile for the actual design** (eq:aniso-profile at a fixed `n`, from
D:601–622 and D:672): for `d ≥ 1`, `0 < α_k < r_k`, the Jackson inequality in every coordinate,
`R ≥ 0`, `f₀` in `C^α_sec([0,1]^d; R)`, any sizes `L`, any enumeration `e` of `C_L` and any design
in the cube, the profile `ProfileAt` holds with `C_sp = 1`, `C_app = 3^{d−1} max_k c_k` and
`E = R`. This is the bridge from Lemma chebyshev-aniso-profile to the hypotheses of Corollary 1. -/
def ChebyshevProfileAtStatement : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (α : Fin d → ℝ) (r : Fin d → ℕ) (CJ : Fin d → ℝ) (R : ℝ)
    (f₀ : (Fin d → ℝ) → ℝ) (n J : ℕ) (L : Fin d → ℕ) (e : Fin J ≃ ChebIdx L)
    (x : Fin n → Fin d → ℝ),
    (∀ k, 0 < α k) → (∀ k, α k < r k) → (∀ k, JacksonIneq (α k) (r k) (CJ k)) → 0 ≤ R →
    SecHolderBall α R f₀ → (∀ i, x i ∈ unitCube d) →
    ProfileAt (chebDesign e x) (fun i => f₀ (x i)) L α 1 (chebCapp hd α r CJ R) R

/-- Hypotheses of the Chebyshev end-to-end corollary, apart from the classical input, `d ≥ 1`
and the dictionary sizes: `α_k > 0`, difference orders `r_k > α_k`, exponents `b_k ≥ β_k`, `R > 0`,
`f₀` in the sectional class of radius `R`, design points in `[0,1]^d`, `σ > 0`, horseshoe constants
`η ∈ (0,1)`, `μ'' > 0`. -/
structure CorChebHyp {d : ℕ} (α b : Fin d → ℝ) (r : Fin d → ℕ) (R : ℝ)
    (f₀ : (Fin d → ℝ) → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (σ η μ'' : ℝ) : Prop where
  hα : ∀ k, 0 < α k
  hr : ∀ k, α k < r k
  hb : ∀ k, betaExp α k ≤ b k
  hR : 0 < R
  hball : SecHolderBall α R f₀
  hx : ∀ n i, x n i ∈ unitCube d
  hσ : 0 < σ
  hη : 0 < η
  hη1 : η < 1
  hμ'' : 0 < μ''

/-- The conclusion of Corollary 1 for a dictionary sequence `X` of sizes `J`, the truth `f₀`
observed at the design `x`, the horseshoe prior with `τ_n = J_n^{−(2+μ'')}/√n`, and constants
`C_sp, E, C_ε, c_δ`, `K = 2^{d/2}`: Assumption 3 holds with `μ = μ''/2`, `c₄ = 1` and some
`c₅ ≥ 0`, Theorem 1 applies for every `M_n → ∞`, and (i)–(iii) of Corollary 1 hold with
`A = Aconst K η σ (μ''/2) 1 c₅` (as in `CorFourierStatement`; the prefactor in (ii) is 5, which
implies the paper's 6, and (WG5) is checked almost everywhere, as in all of `CorSpec`).
As in `CorFourierStatement`, the prior is specialised to the horseshoe with this scale (the
general-prior Corollary 1 is `CorollaryStatement`, which applies to the Chebyshev dictionary
through `ChebyshevBasisStatement` and `ChebyshevProfileAtStatement`), and `c₅` is chosen after the
truth and the design (Corollary 1 is pointwise in `f₀`, S:143–200). -/
def CorChebOutcome {d : ℕ} (α : Fin d → ℝ) (J : ℕ → ℕ)
    (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : (Fin d → ℝ) → ℝ)
    (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (σ η μ'' cδ Csp E Ceps : ℝ) : Prop :=
  ∃ c5 : ℝ, 0 ≤ c5 ∧
    (∀ M : ℕ → ℝ, Tendsto M atTop atTop →
      CorTheorem1Inputs α J X (fun n i => f₀ (x n i)) σ
        (fun n => horseshoePDF (corTau μ'' n (J n))) Csp E Ceps cδ
        (Real.sqrt 2 ^ d) η (μ'' / 2) 1 c5 M) ∧
    CorConclusion α J X (fun n i => f₀ (x n i)) σ
      (fun n => horseshoePDF (corTau μ'' n (J n))) Csp Ceps cδ
      (Aconst (Real.sqrt 2 ^ d) η σ (μ'' / 2) 1 c5)

/-- Corollary 1 for the tensor Chebyshev dictionary at fixed `(d, α, r, C_J)`, with the paper's
explicit constants (S:169 with D:621): for every `R > 0` and every `C_ε ≥ d C_app`,
`C_app = 3^{d−1} max_k c_k`, every exponent `b_k ≥ β_k`, all sizes `L_{n,k}` and totals `J_n` with
`L_{n,k} ≍ n^{b_k}` and `J_n ≍ ∏_k L_{n,k}` (`SizesComparable`), every enumeration
`e_n : Fin J_n ≃ C_{L_n}`, every `f₀` in `C^α_sec([0,1]^d; R)`, every design in the cube, and every
`c_δ ∈ (0,1)`, the conclusion holds with `C_sp = 1` and `E = R`. Comparability is eventual, so a
finite prefix of sizes (even zero ones) is unconstrained; `e_n` fixes `J_n = ∏_k L_{n,k}`. -/
def CorChebExplicit (d : ℕ) (hd : 0 < d) (α : Fin d → ℝ) (r : Fin d → ℕ) (CJ : Fin d → ℝ) :
    Prop :=
  ∀ (R Ceps : ℝ), (d : ℝ) * chebCapp hd α r CJ R ≤ Ceps →
    ∀ (b : Fin d → ℝ) (J : ℕ → ℕ) (L : ℕ → Fin d → ℕ) (e : ∀ n, Fin (J n) ≃ ChebIdx (L n))
      (f₀ : (Fin d → ℝ) → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (σ η μ'' cδ : ℝ),
      CorChebHyp α b r R f₀ x σ η μ'' → SizesComparable b L J → 0 < cδ → cδ < 1 →
      CorChebOutcome α J (chebXe e x) f₀ x σ η μ'' cδ 1 R Ceps

/-- **Corollary 1, tensor Chebyshev dictionary, horseshoe prior, explicit constants**
(S:143–204 with D:601–622): given the Jackson inequality in every coordinate, `CorChebExplicit`. -/
def CorChebyshevStatement : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (α : Fin d → ℝ) (r : Fin d → ℕ) (CJ : Fin d → ℝ),
    (∀ k, JacksonIneq (α k) (r k) (CJ k)) → CorChebExplicit d hd α r CJ

/-- **Corollary 1, tensor Chebyshev dictionary, horseshoe prior**, in the existential-constant
shape of `CorFourierStatement`, with the canonical sizes `L_{n,k} = ⌈n^{b_k}⌉`: given the Jackson
inequality in every coordinate, there are `C_sp, C_ε, E > 0`, depending only on
`(d, α, r, C_J, R)`, such that the conclusion holds for every admissible exponent, `f₀`, design
in the cube, prior constants and `c_δ ∈ (0,1)`. A convenience form, implied by
`CorChebyshevStatement` (which carries the paper's values `C_sp = 1`, `E = R`, `C_ε ≥ d C_app`). -/
def CorChebyshevExStatement : Prop :=
  ∀ (d : ℕ) (α : Fin d → ℝ) (r : Fin d → ℕ) (CJ : Fin d → ℝ) (R : ℝ),
    0 < d → (∀ k, JacksonIneq (α k) (r k) (CJ k)) → (∀ k, 0 < α k) → (∀ k, α k < r k) →
    0 < R →
    ∃ Csp Ceps E : ℝ, 0 < Csp ∧ 0 < Ceps ∧ 0 < E ∧
      ∀ (b : Fin d → ℝ) (f₀ : (Fin d → ℝ) → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ)
        (σ η μ'' cδ : ℝ),
        CorChebHyp α b r R f₀ x σ η μ'' → 0 < cδ → cδ < 1 →
        CorChebOutcome α (chebJ b) (chebX b x) f₀ x σ η μ'' cδ Csp E Ceps

/-- **Corollary 1, tensor Chebyshev dictionary, `α ∈ (0,1)^d`, with no assumed classical
input**: there are Jackson constants `C_J`, depending only on `α`, for which the Jackson
inequality at order `r = 1` holds (by `jackson_lip`, Jackson.lean:301), and Corollary 1 holds with
the explicit constants of `CorChebExplicit` at `r = 1`. -/
def CorChebyshevHolderStatement : Prop :=
  ∀ (d : ℕ) (hd : 0 < d) (α : Fin d → ℝ), (∀ k, 0 < α k) → (∀ k, α k < 1) →
    ∃ CJ : Fin d → ℝ, (∀ k, JacksonIneq (α k) 1 (CJ k)) ∧ CorChebExplicit d hd α (fun _ => 1) CJ

/-! ## Sanity statements (proved in `ChebChecks`; a failure means a definition is wrong) -/

/-- For `0 < α ≤ 1`, the class `HolderBallIcc` is the Hölder ball `HolderBall1` of CorSpec. -/
def ChebSanityHolder : Prop :=
  ∀ (α R : ℝ) (f : ℝ → ℝ), 0 < α → α ≤ 1 → (HolderBallIcc α R f ↔ HolderBall1 α R f)

/-- The four values of D:512 for the smallest order `r = ⌊α⌋ + 1`:
`C_tr(½) = 1 + √π`, `C_tr(1) = 1 + 2π`, `C_tr(2) = 1 + 6π²`, `C_tr(3) = 1 + 22π³`. -/
def ChebSanityCtr : Prop :=
  chebCtr (1 / 2) (⌊(1 / 2 : ℝ)⌋₊ + 1) = 1 + Real.sqrt Real.pi ∧
    chebCtr 1 (⌊(1 : ℝ)⌋₊ + 1) = 1 + 2 * Real.pi ∧
    chebCtr 2 (⌊(2 : ℝ)⌋₊ + 1) = 1 + 6 * Real.pi ^ 2 ∧
    chebCtr 3 (⌊(3 : ℝ)⌋₊ + 1) = 1 + 22 * Real.pi ^ 3

/-- The anisotropic lemma at `d = 1` implies the univariate lemma (with the same constant, since
`3^0 max_k c_k = c_1 = C R`). -/
def ChebSanityAnisoUniv : Prop :=
  ChebyshevAnisoProfileStatement → ChebyshevProfileStatement

end LargePrior
