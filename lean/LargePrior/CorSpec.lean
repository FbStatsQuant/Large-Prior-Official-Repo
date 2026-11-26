import LargePrior.Spec

/-!
# LargePrior: specification of Corollary 1 and the sparse approximation lemmas

Definitions and main statements (as `Prop`s) for the Lean formalization of Corollary 1 of
*Large series priors for adaptive and optimal Bayesian nonparametric regression*, of its
proof (Appendix B), and of the two sparse approximation lemmas of Appendix D (B-spline and
Fourier dictionaries).

Classical approximation theorems are *not* proved here. They enter as named hypotheses:
* `JacksonIneq`: the periodic Jackson(–Stechkin) inequality (Fourier lemma);
* `BSplineReadout`: uniform sup-norm stability of the B-spline basis (Schumaker Thm 4.41);
* `SplineOneBlock`, `SplineOneBlockCube`: the one-block spline approximation theorems
  (Schumaker Thm 6.10 / 12.7, Shen–Ghosal 2015 Lemma 2 and Remark 7), applied to `f₀`.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

/-! ## Exponents (eq:aniso-exponents, eq:aniso-beta) -/

/-- Harmonic-mean smoothness `α* = d / ∑_k α_k⁻¹`. -/
def alphaStar {d : ℕ} (α : Fin d → ℝ) : ℝ := d / ∑ k, (α k)⁻¹

/-- Rate exponent `r = α* / (2α* + d)`. -/
def rateExp {d : ℕ} (α : Fin d → ℝ) : ℝ := alphaStar α / (2 * alphaStar α + d)

/-- Dimension exponent `D = d / (2α* + d)`. -/
def dimExp {d : ℕ} (α : Fin d → ℝ) : ℝ := d / (2 * alphaStar α + d)

/-- Budget exponents `β_k = α* / (α_k (2α* + d))`. -/
def betaExp {d : ℕ} (α : Fin d → ℝ) (k : Fin d) : ℝ :=
  alphaStar α / (α k * (2 * alphaStar α + d))

/-! ## The corollary's sequences (eq:aniso-choice, eq:aniso-prior-choice) -/

/-- `N_n = n / log J_n`. -/
def corN (n J : ℕ) : ℝ := n / Real.log J

/-- Balanced term budget `m_{n,k} = ⌈N_n^{β_k}⌉`. -/
def corM {d : ℕ} (α : Fin d → ℝ) (n J : ℕ) (k : Fin d) : ℕ := ⌈corN n J ^ betaExp α k⌉₊

/-- Effective sparsity `a_n = ⌈C_sp ∏_k m_{n,k}⌉`. -/
def corA {d : ℕ} (Csp : ℝ) (α : Fin d → ℝ) (n J : ℕ) : ℕ :=
  ⌈Csp * ∏ k, (corM α n J k : ℝ)⌉₊

/-- Approximation accuracy `ε̃_n = C_ε N_n^{−r}`. -/
def corEpsT {d : ℕ} (Ceps : ℝ) (α : Fin d → ℝ) (n J : ℕ) : ℝ :=
  Ceps * corN n J ^ (-rateExp α)

/-- Negligibility threshold `δ_n = c_δ ε̃_n / J_n`. -/
def corDelta {d : ℕ} (cδ Ceps : ℝ) (α : Fin d → ℝ) (n J : ℕ) : ℝ :=
  cδ * corEpsT Ceps α n J / J

/-- The target rate `(n / log n)^{−r}`. -/
def corRate {d : ℕ} (α : Fin d → ℝ) (n : ℕ) : ℝ := ((n : ℝ) / Real.log n) ^ (-rateExp α)

/-! ## The sparse approximation profile (eq:aniso-profile) -/

/-- Size of the support `#{j : θ_j ≠ 0}` of a coefficient vector on a finite index type. -/
def suppCard {ι : Type*} [Fintype ι] (θ : ι → ℝ) : ℕ := (univ.filter fun j => θ j ≠ 0).card

/-- The sparse approximation profile at a fixed `n` (eq:aniso-profile), for a dictionary
matrix `X` with coordinate sizes `L_k`: for every integer rectangle `1 ≤ m_k ≤ L_k` there is
`θ(m)` with `#supp θ(m) ≤ C_sp ∏_k m_k`, `‖f₀ − f_{θ(m)}‖_{2,n} ≤ C_app ∑_k m_k^{−α_k}`, and
`‖θ(m)‖_∞ ≤ E`. -/
def ProfileAt {n J d : ℕ} (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (L : Fin d → ℕ)
    (α : Fin d → ℝ) (Csp Capp E : ℝ) : Prop :=
  ∀ m : Fin d → ℕ, (∀ k, 1 ≤ m k ∧ m k ≤ L k) →
    ∃ θ : Fin J → ℝ, (suppCard θ : ℝ) ≤ Csp * ∏ k, (m k : ℝ) ∧
      empNorm (f₀ - X *ᵥ θ) ≤ Capp * ∑ k, (m k : ℝ) ^ (-α k) ∧ ∀ j, |θ j| ≤ E

/-- Dictionary sizes: `L_{n,k} ≍ n^{b_k}` and `J_n ≍ ∏_k L_{n,k}`, i.e. there are constants
`c > 0` and `C` with `c n^{b_k} ≤ L_{n,k} ≤ C n^{b_k}` and `c ∏_k L_{n,k} ≤ J_n ≤ C ∏_k L_{n,k}`
for all sufficiently large `n`. -/
def SizesComparable {d : ℕ} (b : Fin d → ℝ) (L : ℕ → Fin d → ℕ) (J : ℕ → ℕ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
    (∀ k, c * (n : ℝ) ^ b k ≤ L n k ∧ (L n k : ℝ) ≤ C * (n : ℝ) ^ b k) ∧
    c * ∏ k, (L n k : ℝ) ≤ J n ∧ (J n : ℝ) ≤ C * ∏ k, (L n k : ℝ)

/-! ## Corollary 1 (abstract form: profile ⇒ rates) -/

/-- Hypotheses of Corollary 1, given the profile. `d ≥ 1` and `α_k > 0` fixed; dictionary
sizes `L_{n,k} ≍ n^{b_k}` with `b_k ≥ β_k`, `J_n ≍ ∏_k L_{n,k}`; Assumption 1 with a fixed `K`;
the profile with fixed constants `C_sp, C_app, E` for all large `n`; the sequence constants
`C_ε ≥ d C_app` ("`C_ε` sufficiently large", the condition the proof uses) and `c_δ ∈ (0,1)`;
and Assumption 3 for the sequences `a_n, ε̃_n, δ_n, E_n = E` of `corA`, `corEpsT`, `corDelta`,
with (WG4) required for one set of size `a_n` (by `wg4_of_card_eq` it then holds for
every set of size `a_n`, in particular for the active set `ξ*_n` built in the proof). -/
structure CorHyp {d : ℕ} (α b : Fin d → ℝ) (L : ℕ → Fin d → ℕ) (J : ℕ → ℕ)
    (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ)
    (pdf : ℕ → ℝ → ℝ) (Csp Capp E Ceps cδ K η μ c4 c5 : ℝ) : Prop where
  hd : 0 < d
  hα : ∀ k, 0 < α k
  hb : ∀ k, betaExp α k ≤ b k
  hsize : SizesComparable b L J
  hσ : 0 < σ
  hK : 0 < K
  hbasis : ∀ᶠ n in atTop, BasisBound (X n) K
  hCsp : 0 < Csp
  hCapp : 0 ≤ Capp
  hE : 0 < E
  hprofile : ∀ᶠ n in atTop, ProfileAt (X n) (f₀ n) (L n) α Csp Capp E
  hCeps : 0 < Ceps
  hCepsApp : (d : ℝ) * Capp ≤ Ceps
  hcδ : 0 < cδ
  hcδ1 : cδ < 1
  hη : 0 < η
  hη1 : η < 1
  hμ : 0 < μ
  hc4 : 0 ≤ c4
  hc5 : 0 ≤ c5
  hpdf : ∀ᶠ n in atTop, IsProbDensity (pdf n)
  h3 : ∀ᶠ n in atTop, WG3 (pdf n) (corDelta cδ Ceps α n (J n)) μ (J n)
  h4 : ∀ᶠ n in atTop, ∃ S : Finset (Fin (J n)), S.card = corA Csp α n (J n) ∧
    WG4 (pdf n) (J n) S η (corEpsT Ceps α n (J n)) c4 n
  h5 : ∀ᶠ n in atTop, WG5 (pdf n) E (corEpsT Ceps α n (J n)) c5 (corA Csp α n (J n)) n

/-! ### The constants of the proof (eq:cor-constants) -/

/-- `C_a = 2^d C_sp + 1` (bounds `a_n / N_n^D`). -/
def corCa (d : ℕ) (Csp : ℝ) : ℝ := 2 ^ d * Csp + 1

/-- `C_s = max{C_a, C_ε² + 1}` (bounds `s_n / N_n^D`). -/
def corCs (d : ℕ) (Csp Ceps : ℝ) : ℝ := max (corCa d Csp) (Ceps ^ 2 + 1)

/-- `A' = A C_s / C_sp`, with `A` the integer of Theorem 1. -/
def corAprime (A d : ℕ) (Csp Ceps : ℝ) : ℝ := A * corCs d Csp Ceps / Csp

/-- `c = C_ε² / C_s` (Appendix B, eq:cor-constants). -/
def corExpConst (d : ℕ) (Csp Ceps : ℝ) : ℝ := Ceps ^ 2 / corCs d Csp Ceps

/-- `{θ : #{j : |θ_j| > δ} > t}` for a real threshold `t` (used with `t = A' a_n`; `A'` need not
be an integer). -/
def denseSetReal {J : ℕ} (δ t : ℝ) : Set (Fin J → ℝ) := {θ | t < (numLarge δ θ : ℝ)}

/-- Conclusions (i)–(iii) of Corollary 1, for a given integer `A` (in `CorollaryStatement`, the
integer `Aconst K η σ μ c₄ c₅` of Theorem 1). Writing `a_n = corA`, `ε̃_n = corEpsT`,
`δ_n = corDelta`, `s_n = sRate`, `ε_n = epsRate`, `ρ_n = corRate`:
(i) orders: for some `C > 0` and all large `n`, `a_n ≤ s_n ≤ C a_n`,
`C⁻¹ (n/log n)^D ≤ a_n ≤ C (n/log n)^D`, `C⁻¹ ρ_n ≤ ε_n ≤ C ρ_n`;
(ii) with the explicit constants `A' = A C_s / C_sp > 0` and `c = C_ε² / C_s > 0` (functions of
`A, C_sp, C_ε, d` only), for every `M_n → ∞` and all large `n`:
`E₀ Π(‖f − f₀‖_{2,n} > M_n ε_n | Y) ≤ 5 e^{−c n ε_n²}` and
`E₀ Π(#{j : |θ_j| > δ_n} > A' a_n | Y) ≤ 2 e^{−c n ε_n²}`;
(iii) both posterior probabilities tend to `0` in `P₀`-probability. -/
def CorConclusion {d : ℕ} (α : Fin d → ℝ) (J : ℕ → ℕ)
    (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ)
    (pdf : ℕ → ℝ → ℝ) (Csp Ceps cδ : ℝ) (A : ℕ) : Prop :=
  (∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop,
      (corA Csp α n (J n) : ℝ) ≤ sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ∧
      (sRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) : ℝ) ≤
        C * corA Csp α n (J n) ∧
      C⁻¹ * ((n : ℝ) / Real.log n) ^ dimExp α ≤ corA Csp α n (J n) ∧
      (corA Csp α n (J n) : ℝ) ≤ C * ((n : ℝ) / Real.log n) ^ dimExp α ∧
      C⁻¹ * corRate α n ≤ epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ∧
      epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ≤ C * corRate α n) ∧
  0 < corAprime A d Csp Ceps ∧ 0 < corExpConst d Csp Ceps ∧
  ∀ M : ℕ → ℝ, Tendsto M atTop atTop → (
    (∀ᶠ n in atTop,
      (∫⁻ y, posterior σ (X n) (f₀ n) (prior (J n) (pdf n)) y
          (farSet (X n) (f₀ n)
            (M n * epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n))))
          ∂(dataLaw σ (f₀ n))
        ≤ ENNReal.ofReal (5 * Real.exp (-(corExpConst d Csp Ceps *
            ((n : ℝ) * epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ^ 2))))) ∧
      (∫⁻ y, posterior σ (X n) (f₀ n) (prior (J n) (pdf n)) y
          (denseSetReal (corDelta cδ Ceps α n (J n))
            (corAprime A d Csp Ceps * corA Csp α n (J n))) ∂(dataLaw σ (f₀ n))
        ≤ ENNReal.ofReal (2 * Real.exp (-(corExpConst d Csp Ceps *
            ((n : ℝ) * epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n)) ^ 2)))))) ∧
    (∀ ζ : ℝ, 0 < ζ → Tendsto (fun n : ℕ => dataLaw σ (f₀ n)
        {y | ENNReal.ofReal ζ < posterior σ (X n) (f₀ n) (prior (J n) (pdf n)) y
          (farSet (X n) (f₀ n)
            (M n * epsRate n (J n) (corA Csp α n (J n)) (corEpsT Ceps α n (J n))))})
        atTop (𝓝 0)) ∧
    (∀ ζ : ℝ, 0 < ζ → Tendsto (fun n : ℕ => dataLaw σ (f₀ n)
        {y | ENNReal.ofReal ζ < posterior σ (X n) (f₀ n) (prior (J n) (pdf n)) y
          (denseSetReal (corDelta cδ Ceps α n (J n))
            (corAprime A d Csp Ceps * corA Csp α n (J n)))}) atTop (𝓝 0)))

/-- The hypotheses of Theorem 1 (`AsymptoticHyp`) for the corollary's sequences
`ε̃_n = corEpsT`, `δ_n = corDelta`, `E_n = E`, `a_n = corA`, for a given `M_n`. In particular
Assumption 2 holds (with an active set `ξ*_n` of exactly `a_n` indices and (WG4) for it), and
the standing requirements `n ε̃_n² → ∞`, `δ_n ≤ ε̃_n / J_n`, `s_n log J_n = o(n)` hold. -/
def CorTheorem1Inputs {d : ℕ} (α : Fin d → ℝ) (J : ℕ → ℕ)
    (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ)
    (pdf : ℕ → ℝ → ℝ) (Csp E Ceps cδ K η μ c4 c5 : ℝ) (M : ℕ → ℝ) : Prop :=
  AsymptoticHyp J X f₀ σ pdf (fun n => corEpsT Ceps α n (J n))
    (fun n => corDelta cδ Ceps α n (J n)) (fun _ => E) M (fun n => corA Csp α n (J n))
    K η μ c4 c5

/-- **Corollary 1, first sentence of the conclusion**: under the corollary's hypotheses,
Assumption 2 and the standing requirements hold, so that Theorem 1 applies (for every
`M_n → ∞`). -/
def CorTheorem1InputsStatement : Prop :=
  ∀ (d : ℕ) (α b : Fin d → ℝ) (L : ℕ → Fin d → ℕ) (J : ℕ → ℕ)
    (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ)
    (pdf : ℕ → ℝ → ℝ) (Csp Capp E Ceps cδ K η μ c4 c5 : ℝ),
    CorHyp α b L J X f₀ σ pdf Csp Capp E Ceps cδ K η μ c4 c5 →
    ∀ M : ℕ → ℝ, Tendsto M atTop atTop →
      CorTheorem1Inputs α J X f₀ σ pdf Csp E Ceps cδ K η μ c4 c5 M

/-- **Corollary 1**, abstract form: under the profile and Assumptions 1 and 3, Assumption 2 and
the standing requirements hold, so that Theorem 1 applies, and (i)–(iii) hold with
`A = Aconst K η σ μ c₄ c₅`, the integer of Theorem 1. -/
def CorollaryStatement : Prop :=
  ∀ (d : ℕ) (α b : Fin d → ℝ) (L : ℕ → Fin d → ℕ) (J : ℕ → ℕ)
    (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ)
    (pdf : ℕ → ℝ → ℝ) (Csp Capp E Ceps cδ K η μ c4 c5 : ℝ),
    CorHyp α b L J X f₀ σ pdf Csp Capp E Ceps cδ K η μ c4 c5 →
    (∀ M : ℕ → ℝ, Tendsto M atTop atTop →
      CorTheorem1Inputs α J X f₀ σ pdf Csp E Ceps cδ K η μ c4 c5 M) ∧
    CorConclusion α J X f₀ σ pdf Csp Ceps cδ (Aconst K η σ μ c4 c5)

/-! ## Corollary 1 with the horseshoe prior -/

/-- Deterministic horseshoe global scale `τ_n = J_n^{−(2+μ'')} / √n`. -/
def corTau (μ'' : ℝ) (n J : ℕ) : ℝ := (J : ℝ) ^ (-(2 + μ'')) / Real.sqrt n

/-- Hypotheses of Corollary 1 for the horseshoe prior with scale `corTau μ''`: those of
`CorHyp` without the prior conditions (WG3)–(WG5), which are derived. -/
structure CorHorseshoeHyp {d : ℕ} (α b : Fin d → ℝ) (L : ℕ → Fin d → ℕ) (J : ℕ → ℕ)
    (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ)
    (Csp Capp E Ceps cδ K η μ'' : ℝ) : Prop where
  hd : 0 < d
  hα : ∀ k, 0 < α k
  hb : ∀ k, betaExp α k ≤ b k
  hsize : SizesComparable b L J
  hσ : 0 < σ
  hK : 0 < K
  hbasis : ∀ᶠ n in atTop, BasisBound (X n) K
  hCsp : 0 < Csp
  hCapp : 0 ≤ Capp
  hE : 0 < E
  hprofile : ∀ᶠ n in atTop, ProfileAt (X n) (f₀ n) (L n) α Csp Capp E
  hCeps : 0 < Ceps
  hCepsApp : (d : ℝ) * Capp ≤ Ceps
  hcδ : 0 < cδ
  hcδ1 : cδ < 1
  hη : 0 < η
  hη1 : η < 1
  hμ'' : 0 < μ''

/-- **Corollary 1 for the horseshoe prior** with the deterministic scale `τ_n = J_n^{−(2+μ'')}/√n`
(which does not depend on the smoothness): Assumption 3 holds with `μ = μ''/2`, `c₄ = 1` and some
`c₅ ≥ 0`, Theorem 1 applies, and (i)–(iii) hold with `A = Aconst K η σ (μ''/2) 1 c₅`. -/
def CorHorseshoeStatement : Prop :=
  ∀ (d : ℕ) (α b : Fin d → ℝ) (L : ℕ → Fin d → ℕ) (J : ℕ → ℕ)
    (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ)
    (Csp Capp E Ceps cδ K η μ'' : ℝ),
    CorHorseshoeHyp α b L J X f₀ σ Csp Capp E Ceps cδ K η μ'' →
    ∃ c5 : ℝ, 0 ≤ c5 ∧
      (∀ M : ℕ → ℝ, Tendsto M atTop atTop →
        CorTheorem1Inputs α J X f₀ σ (fun n => horseshoePDF (corTau μ'' n (J n))) Csp E Ceps cδ
          K η (μ'' / 2) 1 c5 M) ∧
      CorConclusion α J X f₀ σ (fun n => horseshoePDF (corTau μ'' n (J n))) Csp Ceps cδ
        (Aconst K η σ (μ'' / 2) 1 c5)

/-! ## Periodic Hölder–Zygmund classes and the Jackson inequality -/

/-- `r`-th forward difference with step `h`:
`Δ_h^r g(x) = ∑_{v=0}^{r} (−1)^{r−v} C(r,v) g(x + v h)`. -/
def fdiff (r : ℕ) (h : ℝ) (g : ℝ → ℝ) (x : ℝ) : ℝ :=
  ∑ v ∈ range (r + 1), (-1 : ℝ) ^ (r - v) * (r.choose v : ℝ) * g (x + v * h)

/-- The section of `f` through `x` in direction `k`: `t ↦ f(x₁,…,x_{k−1},t,x_{k+1},…,x_d)`. -/
def sectionAt {d : ℕ} (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (k : Fin d) : ℝ → ℝ :=
  fun t => f (Function.update x k t)

/-- Ball of radius `R` of the univariate periodic Hölder–Zygmund class of order `α` with
difference order `r`: `g` continuous and 1-periodic with
`‖g‖_∞ + sup_{0<|h|≤1/2} |h|^{−α} ‖Δ_h^r g‖_∞ ≤ R`, written with explicit bounds `A + B ≤ R`. -/
def HZBall1 (α : ℝ) (r : ℕ) (R : ℝ) (g : ℝ → ℝ) : Prop :=
  Continuous g ∧ Function.Periodic g 1 ∧
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ A + B ≤ R ∧ (∀ x, |g x| ≤ A) ∧
      ∀ h x : ℝ, 0 < |h| → |h| ≤ 1 / 2 → |fdiff r h g x| ≤ B * |h| ^ α

/-- Ball of radius `R` of the coordinatewise periodic anisotropic Hölder–Zygmund class:
`f` continuous on `ℝ^d`, 1-periodic in every coordinate, and
`‖f‖_∞ + max_k sup_{0<|h|≤1/2} |h|^{−α_k} ‖Δ_{h e_k}^{r_k} f‖_∞ ≤ R`
(`Δ_{h e_k}^{r} f(x) = Δ_h^{r}` of the section of `f` through `x` in direction `k`, at `x_k`). -/
def HZBall {d : ℕ} (α : Fin d → ℝ) (r : Fin d → ℕ) (R : ℝ) (f : (Fin d → ℝ) → ℝ) : Prop :=
  Continuous f ∧ (∀ (k : Fin d) (x : Fin d → ℝ), f (x + Pi.single k 1) = f x) ∧
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ A + B ≤ R ∧ (∀ x, |f x| ≤ A) ∧
      ∀ (k : Fin d) (x : Fin d → ℝ) (h : ℝ), 0 < |h| → |h| ≤ 1 / 2 →
        |fdiff (r k) h (sectionAt f x k) (x k)| ≤ B * |h| ^ α k

/-- `p` is a real trigonometric polynomial of degree at most `q`: a combination of the atoms
`ψ₀, …, ψ_{2q}` (frequencies `0, …, q`). -/
def IsTrigPoly (q : ℕ) (p : ℝ → ℝ) : Prop :=
  ∃ c : ℕ → ℝ, ∀ x, p x = ∑ ν ∈ range (2 * q + 1), c ν * fourierAtom ν x

/-- **Classical input (periodic Jackson inequality, Jackson–Stechkin).** Every `g` in the
univariate Hölder–Zygmund ball of radius `R` (order `α`, difference order `r`) is approximated
by a trigonometric polynomial of degree at most `q` to within `C R q^{−α}`, for every `q ≥ 1`. -/
def JacksonIneq (α : ℝ) (r : ℕ) (C : ℝ) : Prop :=
  ∀ (R : ℝ) (g : ℝ → ℝ), HZBall1 α r R g → ∀ q : ℕ, 1 ≤ q →
    ∃ p : ℝ → ℝ, IsTrigPoly q p ∧ ∀ x, |g x - p x| ≤ C * R * (q : ℝ) ^ (-α)

/-! ## The Fourier dictionary and Lemma fourier-profile -/

/-- Index set of the tensor Fourier dictionary `F_M`: `ν_k ∈ {0, …, 2M_k}`. -/
abbrev FourierIdx {d : ℕ} (M : Fin d → ℕ) := (k : Fin d) → Fin (2 * M k + 1)

/-- `f_θ = ∑_ν θ_ν Ψ_ν` over the tensor Fourier dictionary `F_M`. -/
def fourierSeries {d : ℕ} {M : Fin d → ℕ} (θ : FourierIdx M → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ ν, θ ν * fourierTensor (fun k => (ν k : ℕ)) x

/-- **Lemma fourier-profile** (sup-norm form). Given the Jackson inequality in every
coordinate, there is `C` depending only on `(d, α, r, C_J)` such that for every `R`, every `f₀`
in the periodic Hölder–Zygmund ball of radius `R`, every dictionary size `M`, and every rectangle
`1 ≤ m_k ≤ 2M_k + 1`, some `θ` has `#supp θ ≤ ∏_k m_k`,
`sup_x |f₀(x) − f_θ(x)| ≤ C R ∑_k m_k^{−α_k}`, and `|θ_ν| ≤ R`. -/
def FourierProfileStatement : Prop :=
  ∀ (d : ℕ) (α : Fin d → ℝ) (r : Fin d → ℕ) (CJ : Fin d → ℝ),
    (∀ k, 0 < α k) → (∀ k, α k < r k) → (∀ k, JacksonIneq (α k) (r k) (CJ k)) →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (R : ℝ) (f₀ : (Fin d → ℝ) → ℝ) (M m : Fin d → ℕ),
      HZBall α r R f₀ → (∀ k, 1 ≤ m k ∧ m k ≤ 2 * M k + 1) →
      ∃ θ : FourierIdx M → ℝ, (suppCard θ : ℝ) ≤ ∏ k, (m k : ℝ) ∧
        (∀ x, |f₀ x - fourierSeries θ x| ≤ C * R * ∑ k, (m k : ℝ) ^ (-α k)) ∧
        ∀ ν, |θ ν| ≤ R

/-! ## The multiresolution B-spline dictionary and Lemma bspline-profile -/

/-- Dimension of the order-`q` spline space at level `ℓ` (`2^ℓ` subintervals):
`D_ℓ = 2^ℓ + q − 1`. -/
def splineDim (q ℓ : ℕ) : ℕ := 2 ^ ℓ + q - 1

/-- Size of the multiresolution union of levels `0, …, H`: `U_H = ∑_{ℓ=0}^{H} D_ℓ`. -/
def splineUnionDim (q H : ℕ) : ℕ := ∑ ℓ ∈ range (H + 1), splineDim q ℓ

/-- The unit cube `[0,1]^d`. -/
def unitCube (d : ℕ) : Set (Fin d → ℝ) := {x | ∀ k, x k ∈ Set.Icc (0 : ℝ) 1}

/-- Tagged index set of the tensor multiresolution dictionary `D_H^{(q)}`: in coordinate `k`, a
level `ℓ ≤ H_k` and a position `i < D_ℓ`. -/
abbrev SplineIdx {d : ℕ} (q : ℕ) (H : Fin d → ℕ) :=
  (k : Fin d) → Σ ℓ : Fin (H k + 1), Fin (splineDim q ℓ)

/-- The atom `∏_k B_{ℓ_k, i_k}(x_k)` of `D_H^{(q)}` (order `q`, `2^{ℓ_k}` subintervals). -/
def splineAtom {d q : ℕ} {H : Fin d → ℕ} (ι : SplineIdx q H) (x : Fin d → ℝ) : ℝ :=
  ∏ k, bspline q (2 ^ ((ι k).1 : ℕ)) ((ι k).2 : ℕ) (x k)

/-- `f_θ = ∑_ι θ_ι · atom_ι` over the multiresolution dictionary. -/
def splineSeries {d q : ℕ} {H : Fin d → ℕ} (θ : SplineIdx q H → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ ι, θ ι * splineAtom ι x

/-- A one-block tensor spline at the levels `ℓ_1, …, ℓ_d`:
`∑_j θ_j ∏_k B_{ℓ_k, j_k}(x_k)`. -/
def blockSeries {d : ℕ} (q : ℕ) (ℓ : Fin d → ℕ)
    (θ : ((k : Fin d) → Fin (splineDim q (ℓ k))) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ j, θ j * ∏ k, bspline q (2 ^ ℓ k) (j k : ℕ) (x k)

/-- **Classical input (B-spline stability, Schumaker Thm 4.41 / de Boor).** Coefficients of a
univariate order-`q` spline at any dyadic level are bounded by `C_dual` times its sup-norm
on `[0,1]`. -/
def BSplineReadout (q : ℕ) (Cdual : ℝ) : Prop :=
  ∀ (ℓ : ℕ) (θ : Fin (splineDim q ℓ) → ℝ) (S : ℝ),
    (∀ x ∈ Set.Icc (0 : ℝ) 1, |∑ i, θ i * bspline q (2 ^ ℓ) (i : ℕ) x| ≤ S) →
    ∀ j, |θ j| ≤ Cdual * S

/-- **Classical input applied to `f₀` (one-block spline approximation, rectangular levels).**
For all levels `ℓ_1, …, ℓ_d` some one-block spline is within `C⋆ ∑_k D_{ℓ_k}^{−α_k}` of `f₀`
on `[0,1]^d`. Holds for `d = 1`, `0 < α ≤ q`, `f₀` in a `C^α([0,1])` ball (Schumaker Thm 6.10),
and for integer `α_k ≤ q` and `f₀` in a ball of the anisotropic class of Appendix D
(Schumaker Thm 12.7; Shen–Ghosal 2015, Lemma 2(a)). -/
def SplineOneBlock {d : ℕ} (q : ℕ) (α : Fin d → ℝ) (Cstar : ℝ) (f₀ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ ℓ : Fin d → ℕ, ∃ θ : ((k : Fin d) → Fin (splineDim q (ℓ k))) → ℝ,
    ∀ x ∈ unitCube d, |f₀ x - blockSeries q ℓ θ x| ≤ Cstar * ∑ k, (splineDim q (ℓ k) : ℝ) ^ (-α k)

/-- **Classical input applied to `f₀` (one-block spline approximation, common level).** For
every common level `ℓ`, some one-block spline is within `C⋆ D_ℓ^{−α}` of `f₀` on `[0,1]^d`.
Holds for `0 < α ≤ q` and `f₀` in a `C^α([0,1]^d)` ball (Shen–Ghosal 2015, Remark 7). -/
def SplineOneBlockCube (d q : ℕ) (α Cstar : ℝ) (f₀ : (Fin d → ℝ) → ℝ) : Prop :=
  ∀ ℓ : ℕ, ∃ θ : ((k : Fin d) → Fin (splineDim q ℓ)) → ℝ,
    ∀ x ∈ unitCube d, |f₀ x - blockSeries q (fun _ => ℓ) θ x| ≤ Cstar * (splineDim q ℓ : ℝ) ^ (-α)

/-- **Lemma bspline-profile, parts 1 and 3** (sup-norm form). Given B-spline stability and the
rectangular one-block approximation of `f₀`, there are `C_sp, C_app, E` depending only on
`(d, q, α, C⋆, C_dual, R)` such that for every truncation `H`, every `f₀` with `|f₀| ≤ R` on the
cube, and every rectangle `1 ≤ m_k ≤ U_{H_k}`, some `θ` on `D_H^{(q)}` has
`#supp θ ≤ C_sp ∏_k m_k`, `sup_{[0,1]^d} |f₀ − f_θ| ≤ C_app ∑_k m_k^{−α_k}`, `|θ_ι| ≤ E`. -/
def BSplineProfileStatement : Prop :=
  ∀ (d q : ℕ) (α : Fin d → ℝ) (Cstar Cdual R : ℝ),
    1 ≤ q → (∀ k, 0 < α k) → 0 ≤ Cstar → 1 ≤ Cdual → BSplineReadout q Cdual →
    ∃ Csp Capp E : ℝ, 0 < Csp ∧ 0 ≤ Capp ∧ 0 < E ∧
      ∀ (H : Fin d → ℕ) (f₀ : (Fin d → ℝ) → ℝ) (m : Fin d → ℕ),
        (∀ x ∈ unitCube d, |f₀ x| ≤ R) → SplineOneBlock q α Cstar f₀ →
        (∀ k, 1 ≤ m k ∧ m k ≤ splineUnionDim q (H k)) →
        ∃ θ : SplineIdx q H → ℝ, (suppCard θ : ℝ) ≤ Csp * ∏ k, (m k : ℝ) ∧
          (∀ x ∈ unitCube d, |f₀ x - splineSeries θ x| ≤ Capp * ∑ k, (m k : ℝ) ^ (-α k)) ∧
          ∀ ι, |θ ι| ≤ E

/-- **Lemma bspline-profile, part 2** (isotropic, sup-norm form, rectangle profile via
`m = min_k m_k`). Same as `BSplineProfileStatement` with `d ≥ 1`, a common truncation
level `H`, scalar smoothness `α`, and the common-level one-block approximation. -/
def BSplineProfileCubeStatement : Prop :=
  ∀ (d q : ℕ) (α Cstar Cdual R : ℝ),
    0 < d → 1 ≤ q → 0 < α → 0 ≤ Cstar → 1 ≤ Cdual → BSplineReadout q Cdual →
    ∃ Csp Capp E : ℝ, 0 < Csp ∧ 0 ≤ Capp ∧ 0 < E ∧
      ∀ (H : ℕ) (f₀ : (Fin d → ℝ) → ℝ) (m : Fin d → ℕ),
        (∀ x ∈ unitCube d, |f₀ x| ≤ R) → SplineOneBlockCube d q α Cstar f₀ →
        (∀ k, 1 ≤ m k ∧ m k ≤ splineUnionDim q H) →
        ∃ θ : SplineIdx q (fun _ : Fin d => H) → ℝ, (suppCard θ : ℝ) ≤ Csp * ∏ k, (m k : ℝ) ∧
          (∀ x ∈ unitCube d, |f₀ x - splineSeries θ x| ≤ Capp * ∑ k, (m k : ℝ) ^ (-α)) ∧
          ∀ ι, |θ ι| ≤ E

/-! ## End-to-end: Corollary 1 for the concrete dictionaries and the horseshoe prior -/

/-- Fourier dictionary size in coordinate `k` at sample size `n`: `M_{n,k} = ⌈n^{b_k}⌉`. -/
def fourierM {d : ℕ} (b : Fin d → ℝ) (n : ℕ) (k : Fin d) : ℕ := ⌈(n : ℝ) ^ b k⌉₊

/-- Total size `J_n = ∏_k (2M_{n,k} + 1)` of the Fourier dictionary. -/
def fourierJ {d : ℕ} (b : Fin d → ℝ) (n : ℕ) : ℕ := Fintype.card (FourierIdx (fourierM b n))

/-- Design matrix of the Fourier dictionary at the design `x n` (columns enumerated by a fixed
bijection `Fin J_n ≃` index set). -/
def fourierX {d : ℕ} (b : Fin d → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin (fourierJ b n)) ℝ :=
  designMatrix (fun j => fourierTensor (fun k => (((Fintype.equivFin _).symm j) k : ℕ))) (x n)

/-- Spline truncation level in coordinate `k`: `H_{n,k} = ⌈b_k log₂ n⌉`. -/
def splineH {d : ℕ} (b : Fin d → ℝ) (n : ℕ) (k : Fin d) : ℕ := ⌈b k * Real.logb 2 n⌉₊

/-- Total size `J_n = ∏_k U_{H_{n,k}}` of the multiresolution B-spline dictionary. -/
def splineJ {d : ℕ} (q : ℕ) (b : Fin d → ℝ) (n : ℕ) : ℕ := Fintype.card (SplineIdx q (splineH b n))

/-- Design matrix of the multiresolution B-spline dictionary at the design `x n`. -/
def splineX {d : ℕ} (q : ℕ) (b : Fin d → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (n : ℕ) :
    Matrix (Fin n) (Fin (splineJ q b n)) ℝ :=
  designMatrix (fun j => splineAtom ((Fintype.equivFin _).symm j)) (x n)

/-- Hypotheses of the Fourier end-to-end corollary, apart from the classical input: `d ≥ 1`,
`α_k > 0`, difference orders `r_k > α_k`, exponents `b_k ≥ β_k`, `f₀` in the periodic
Hölder–Zygmund ball, arbitrary design points, `σ > 0`, horseshoe constants `η ∈ (0,1)`, `μ'' > 0`. -/
structure CorFourierHyp {d : ℕ} (α b : Fin d → ℝ) (r : Fin d → ℕ) (R : ℝ)
    (f₀ : (Fin d → ℝ) → ℝ) (σ η μ'' : ℝ) : Prop where
  hd : 0 < d
  hα : ∀ k, 0 < α k
  hr : ∀ k, α k < r k
  hb : ∀ k, betaExp α k ≤ b k
  hball : HZBall α r R f₀
  hσ : 0 < σ
  hη : 0 < η
  hη1 : η < 1
  hμ'' : 0 < μ''

/-- **Corollary 1, Fourier dictionary, horseshoe prior.** Given the Jackson inequality in every
coordinate, there are constants `C_sp, C_ε > 0`, depending only on `(d, α, r, C_J, R)`, such that
for every exponent `b_k ≥ β_k`, every `f₀` in the periodic Hölder–Zygmund ball of radius `R`, every
design, the Fourier dictionary with `M_{n,k} = ⌈n^{b_k}⌉`, the horseshoe prior with
`τ_n = J_n^{−(2+μ'')}/√n`, and every `c_δ ∈ (0,1)`, the conclusions of Corollary 1 hold. -/
def CorFourierStatement : Prop :=
  ∀ (d : ℕ) (α : Fin d → ℝ) (r : Fin d → ℕ) (CJ : Fin d → ℝ) (R : ℝ),
    (∀ k, JacksonIneq (α k) (r k) (CJ k)) → (∀ k, 0 < α k) → (∀ k, α k < r k) →
    ∃ Csp Ceps E : ℝ, 0 < Csp ∧ 0 < Ceps ∧ 0 < E ∧
      ∀ (b : Fin d → ℝ) (f₀ : (Fin d → ℝ) → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ)
        (σ η μ'' cδ : ℝ),
        CorFourierHyp α b r R f₀ σ η μ'' → 0 < cδ → cδ < 1 →
        ∃ c5 : ℝ, 0 ≤ c5 ∧
          (∀ M : ℕ → ℝ, Tendsto M atTop atTop →
            CorTheorem1Inputs α (fourierJ b) (fourierX b x) (fun n i => f₀ (x n i)) σ
              (fun n => horseshoePDF (corTau μ'' n (fourierJ b n))) Csp E Ceps cδ
              (Real.sqrt 2 ^ d) η (μ'' / 2) 1 c5 M) ∧
          CorConclusion α (fourierJ b) (fourierX b x) (fun n i => f₀ (x n i)) σ
            (fun n => horseshoePDF (corTau μ'' n (fourierJ b n))) Csp Ceps cδ
            (Aconst (Real.sqrt 2 ^ d) η σ (μ'' / 2) 1 c5)

/-- Hypotheses of the B-spline end-to-end corollary (rectangular levels), apart from the
classical inputs: `d ≥ 1`, order `q ≥ 1`, `α_k > 0`, `b_k ≥ β_k`, `|f₀| ≤ R` on `[0,1]^d`,
design points in `[0,1]^d`, `σ > 0`, horseshoe constants `η ∈ (0,1)`, `μ'' > 0`. -/
structure CorBSplineHyp {d : ℕ} (q : ℕ) (α b : Fin d → ℝ) (R : ℝ) (f₀ : (Fin d → ℝ) → ℝ)
    (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (σ η μ'' : ℝ) : Prop where
  hd : 0 < d
  hq : 1 ≤ q
  hα : ∀ k, 0 < α k
  hb : ∀ k, betaExp α k ≤ b k
  hf₀ : ∀ y ∈ unitCube d, |f₀ y| ≤ R
  hx : ∀ n i, x n i ∈ unitCube d
  hσ : 0 < σ
  hη : 0 < η
  hη1 : η < 1
  hμ'' : 0 < μ''

/-- **Corollary 1, multiresolution B-spline dictionary (rectangular levels), horseshoe prior.**
Given B-spline stability, there are `C_sp, C_ε > 0`, depending only on `(d, q, α, C⋆, C_dual, R)`,
such that for every `f₀` with the rectangular one-block approximation property (classical for
`d = 1`, and for the integer anisotropic class) and every admissible exponent, design in the cube,
prior constants, and `c_δ ∈ (0,1)`, with `H_{n,k} = ⌈b_k log₂ n⌉`, the conclusions of Corollary 1
hold. -/
def CorBSplineStatement : Prop :=
  ∀ (d q : ℕ) (α : Fin d → ℝ) (Cstar Cdual R : ℝ),
    1 ≤ q → (∀ k, 0 < α k) → 0 ≤ Cstar → 1 ≤ Cdual → BSplineReadout q Cdual →
    ∃ Csp Ceps E : ℝ, 0 < Csp ∧ 0 < Ceps ∧ 0 < E ∧
      ∀ (b : Fin d → ℝ) (f₀ : (Fin d → ℝ) → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ)
        (σ η μ'' cδ : ℝ),
        SplineOneBlock q α Cstar f₀ → CorBSplineHyp q α b R f₀ x σ η μ'' → 0 < cδ → cδ < 1 →
        ∃ c5 : ℝ, 0 ≤ c5 ∧
          (∀ M : ℕ → ℝ, Tendsto M atTop atTop →
            CorTheorem1Inputs α (splineJ q b) (splineX q b x) (fun n i => f₀ (x n i)) σ
              (fun n => horseshoePDF (corTau μ'' n (splineJ q b n))) Csp E Ceps cδ
              1 η (μ'' / 2) 1 c5 M) ∧
          CorConclusion α (splineJ q b) (splineX q b x) (fun n i => f₀ (x n i)) σ
            (fun n => horseshoePDF (corTau μ'' n (splineJ q b n))) Csp Ceps cδ
            (Aconst 1 η σ (μ'' / 2) 1 c5)

/-- **Corollary 1, isotropic B-spline case, horseshoe prior.** As `CorBSplineStatement` with
`d ≥ 1`, scalar smoothness `α` (so `α_k = α`), a common exponent `b ≥ 1/(2α + d)`, and the
common-level one-block approximation (classical for `0 < α ≤ q` and `f₀` in a `C^α([0,1]^d)`
ball). -/
def CorBSplineCubeStatement : Prop :=
  ∀ (d q : ℕ) (α Cstar Cdual R : ℝ),
    0 < d → 1 ≤ q → 0 < α → 0 ≤ Cstar → 1 ≤ Cdual → BSplineReadout q Cdual →
    ∃ Csp Ceps E : ℝ, 0 < Csp ∧ 0 < Ceps ∧ 0 < E ∧
      ∀ (b : ℝ) (f₀ : (Fin d → ℝ) → ℝ) (x : ∀ n : ℕ, Fin n → Fin d → ℝ) (σ η μ'' cδ : ℝ),
        SplineOneBlockCube d q α Cstar f₀ →
        CorBSplineHyp q (fun _ => α) (fun _ => b) R f₀ x σ η μ'' → 0 < cδ → cδ < 1 →
        ∃ c5 : ℝ, 0 ≤ c5 ∧
          (∀ M : ℕ → ℝ, Tendsto M atTop atTop →
            CorTheorem1Inputs (fun _ : Fin d => α) (splineJ q fun _ : Fin d => b)
              (splineX q (fun _ : Fin d => b) x) (fun n i => f₀ (x n i)) σ
              (fun n => horseshoePDF (corTau μ'' n (splineJ q (fun _ : Fin d => b) n))) Csp E Ceps cδ
              1 η (μ'' / 2) 1 c5 M) ∧
          CorConclusion (fun _ : Fin d => α) (splineJ q fun _ : Fin d => b)
            (splineX q (fun _ : Fin d => b) x) (fun n i => f₀ (x n i)) σ
            (fun n => horseshoePDF (corTau μ'' n (splineJ q (fun _ : Fin d => b) n))) Csp Ceps cδ
            (Aconst 1 η σ (μ'' / 2) 1 c5)

/-! ## Univariate Hölder functions with `0 < α ≤ 1`: no classical input -/

/-- Ball of radius `R` of the univariate Hölder class `C^α([0,1])`, `0 < α ≤ 1` (at `α = 1` the
Lipschitz class, the manuscript's convention `C^1 = C^{0,1}`): `|f| ≤ R` and
`|f(x) − f(y)| ≤ R |x − y|^α` on `[0,1]`. -/
def HolderBall1 (α R : ℝ) (f : ℝ → ℝ) : Prop :=
  (∀ x ∈ Set.Icc (0 : ℝ) 1, |f x| ≤ R) ∧
    ∀ x ∈ Set.Icc (0 : ℝ) 1, ∀ y ∈ Set.Icc (0 : ℝ) 1, |f x - f y| ≤ R * |x - y| ^ α

/-- **Corollary 1 for every univariate `α`-Hölder function, `0 < α ≤ 1`, with order-1
multiresolution B-splines and the horseshoe prior, with no assumed classical input.** For fixed
`0 < α ≤ 1` and `R ≥ 0` there are `C_sp, C_ε > 0` such that for every `f₀` in the `C^α([0,1])` ball
of radius `R`, every exponent `b ≥ 1/(2α + 1)`, every design in `[0,1]`, and all `σ > 0`,
`η ∈ (0,1)`, `μ'' > 0`, `c_δ ∈ (0,1)`, the conclusions of Corollary 1 hold; in particular the
posterior contracts at `M_n (n/log n)^{−α/(2α+1)}`. -/
def CorHolderStatement : Prop :=
  ∀ (α R : ℝ), 0 < α → α ≤ 1 → 0 ≤ R →
    ∃ Csp Ceps E : ℝ, 0 < Csp ∧ 0 < Ceps ∧ 0 < E ∧
      ∀ (b : ℝ) (f₀ : ℝ → ℝ) (x : ∀ n : ℕ, Fin n → Fin 1 → ℝ) (σ η μ'' cδ : ℝ),
        HolderBall1 α R f₀ → 1 / (2 * α + 1) ≤ b → (∀ n i, x n i ∈ unitCube 1) →
        0 < σ → 0 < η → η < 1 → 0 < μ'' → 0 < cδ → cδ < 1 →
        ∃ c5 : ℝ, 0 ≤ c5 ∧
          (∀ M : ℕ → ℝ, Tendsto M atTop atTop →
            CorTheorem1Inputs (fun _ : Fin 1 => α) (splineJ 1 fun _ : Fin 1 => b)
              (splineX 1 (fun _ : Fin 1 => b) x) (fun n i => f₀ (x n i 0)) σ
              (fun n => horseshoePDF (corTau μ'' n (splineJ 1 (fun _ : Fin 1 => b) n))) Csp E Ceps cδ
              1 η (μ'' / 2) 1 c5 M) ∧
          CorConclusion (fun _ : Fin 1 => α) (splineJ 1 fun _ : Fin 1 => b)
            (splineX 1 (fun _ : Fin 1 => b) x) (fun n i => f₀ (x n i 0)) σ
            (fun n => horseshoePDF (corTau μ'' n (splineJ 1 (fun _ : Fin 1 => b) n))) Csp Ceps cδ
            (Aconst 1 η σ (μ'' / 2) 1 c5)

end LargePrior
