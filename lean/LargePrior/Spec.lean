import Mathlib

/-!
# LargePrior: specification

Definitions and the main statements (as `Prop`s) for the Lean formalization of Theorem 1 of
*Large series priors for adaptive and optimal Bayesian nonparametric regression*,
of the horseshoe verification of its prior
conditions (WG3)–(WG5), and of the basis condition (Assumption 1) for Fourier and B-spline
dictionaries.

Everything is stated on evaluation vectors: a function is identified with its values at the
`n` design points, so `f₀ : Fin n → ℝ` and the dictionary is the `n × J` matrix
`X i j = ξ_j(x_i)`; `f_θ = X *ᵥ θ`.

Lean conventions to keep in mind (see `docs/statements.md`):
* `Fin n → ℝ` carries the sup norm in Mathlib, so the empirical norm is the explicit `empNorm`.
* Prior and posterior probabilities are `ℝ≥0∞`-valued measures; no `toReal` is taken.
-/

open MeasureTheory ProbabilityTheory Filter Finset
open scoped ENNReal NNReal Topology Matrix

noncomputable section

namespace LargePrior

/-! ## Empirical geometry -/

/-- Empirical norm `‖u‖_{2,n} = (n⁻¹ ∑ᵢ uᵢ²)^{1/2}` on `ℝⁿ`. -/
def empNorm {n : ℕ} (u : Fin n → ℝ) : ℝ := Real.sqrt ((∑ i, u i ^ 2) / n)

/-- `N(θ) = #{j : |θ_j| > δ}`, the number of non-negligible coordinates. -/
def numLarge {J : ℕ} (δ : ℝ) (θ : Fin J → ℝ) : ℕ := (univ.filter (fun j => δ < |θ j|)).card

/-! ## Prior -/

/-- `pdf` is a probability density on `ℝ`. -/
structure IsProbDensity (pdf : ℝ → ℝ) : Prop where
  measurable : Measurable pdf
  nonneg : ∀ t, 0 ≤ pdf t
  lintegral_eq_one : ∫⁻ t, ENNReal.ofReal (pdf t) = 1

/-- One coordinate of the prior: Lebesgue measure with density `pdf`. -/
def coordPrior (pdf : ℝ → ℝ) : Measure ℝ := volume.withDensity (fun t => ENNReal.ofReal (pdf t))

/-- The coefficient prior `Π_n = ⊗_{j=1}^{J} Π_{n,j}`, coordinates iid with density `pdf`. -/
def prior (J : ℕ) (pdf : ℝ → ℝ) : Measure (Fin J → ℝ) :=
  Measure.pi (fun _ : Fin J => coordPrior pdf)

/-! ## Data, likelihood ratio, evidence, posterior -/

/-- `P_v`: the law of `Y = v + ε` with `εᵢ` iid `N(0, σ²)`. -/
def dataLaw {n : ℕ} (σ : ℝ) (v : Fin n → ℝ) : Measure (Fin n → ℝ) :=
  Measure.pi (fun i => gaussianReal (v i) (Real.toNNReal (σ ^ 2)))

/-- The Gaussian likelihood ratio `(p_g / p_{f₀})(y)`, in closed form:
`exp(σ⁻² ∑ᵢ (yᵢ − f₀ᵢ)(gᵢ − f₀ᵢ) − (2σ²)⁻¹ ∑ᵢ (gᵢ − f₀ᵢ)²)`. -/
def likRatio {n : ℕ} (σ : ℝ) (f₀ g y : Fin n → ℝ) : ℝ :=
  Real.exp ((∑ i, (y i - f₀ i) * (g i - f₀ i)) / σ ^ 2 - (∑ i, (g i - f₀ i) ^ 2) / (2 * σ ^ 2))

/-- The evidence `D_n(y) = ∫ L_n(θ)(y) dΠ(θ)`. -/
def evidence {n J : ℕ} (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (pri : Measure (Fin J → ℝ)) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ∫⁻ θ, ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y) ∂pri

/-- The posterior given data `y`, by Bayes' formula:
`Π(H | y) = ∫_H L_n(θ)(y) dΠ(θ) / D_n(y)`. -/
def posterior {n J : ℕ} (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (pri : Measure (Fin J → ℝ)) (y : Fin n → ℝ) : Measure (Fin J → ℝ) :=
  (evidence σ X f₀ pri y)⁻¹ • pri.withDensity (fun θ => ENNReal.ofReal (likRatio σ f₀ (X *ᵥ θ) y))

/-- `U_n = {θ : ‖f_θ − f₀‖_{2,n} > r}` (used with `r = M_n ε_n`). -/
def farSet {n J : ℕ} (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (r : ℝ) :
    Set (Fin J → ℝ) := {θ | r < empNorm (X *ᵥ θ - f₀)}

/-- `Θ_nᶜ = {θ : N(θ) > m}` (used with `m = A s_n`). -/
def denseSet {J : ℕ} (δ : ℝ) (m : ℕ) : Set (Fin J → ℝ) := {θ | m < numLarge δ θ}

/-! ## Rate sequences and constants -/

/-- `s_n = max{a_n, ⌈n ε̃_n² / log J_n⌉}`. -/
def sRate (n J a : ℕ) (εt : ℝ) : ℕ := max a ⌈(n : ℝ) * εt ^ 2 / Real.log J⌉₊

/-- `ε_n = (s_n log J_n / n)^{1/2}`. -/
def epsRate (n J a : ℕ) (εt : ℝ) : ℝ := Real.sqrt ((sRate n J a εt : ℝ) * Real.log J / n)

/-- `L̃ = 1 + K(1 + 2η)`. -/
def Ltil (K η : ℝ) : ℝ := 1 + K * (1 + 2 * η)

/-- `C₀ = √2 L̃ / σ + L̃² / (2σ²)`. -/
def C0 (K η σ : ℝ) : ℝ := Real.sqrt 2 * Ltil K η / σ + Ltil K η ^ 2 / (2 * σ ^ 2)

/-- `C_Π = c₄ + c₅ + 1`. -/
def CPi (c4 c5 : ℝ) : ℝ := c4 + c5 + 1

/-- `C₁ = C_Π + C₀`. -/
def C1 (K η σ c4 c5 : ℝ) : ℝ := CPi c4 c5 + C0 K η σ

/-- `A = ⌈(C₁ + 1)/μ⌉`. -/
def Aconst (K η σ μ c4 c5 : ℝ) : ℕ := ⌈(C1 K η σ c4 c5 + 1) / μ⌉₊

/-! ## Assumptions at a fixed sample size -/

/-- Assumption 1 (basis) at a fixed `n`: `max_j ‖ξ_j‖_{2,n} ≤ K`. -/
def BasisBound {n J : ℕ} (X : Matrix (Fin n) (Fin J) ℝ) (K : ℝ) : Prop :=
  ∀ j, empNorm (fun i => X i j) ≤ K

/-- Assumption 2 (sparse approximability) at a fixed `n`, for the approximant `θ₀` and the
fixed active set `S = ξ*_n`: `‖f₀ − f_{θ₀}‖_{2,n} ≤ ε̃`, `#{j : |θ₀ⱼ| > δ} ≤ a`, `max_j |θ₀ⱼ| ≤ E`,
`|S| = a`, and `|θ₀ⱼ| ≤ δ` for `j ∉ S`. -/
def SparseApprox {n J : ℕ} (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (εt δ E : ℝ) (a : ℕ)
    (θ₀ : Fin J → ℝ) (S : Finset (Fin J)) : Prop :=
  empNorm (f₀ - X *ᵥ θ₀) ≤ εt ∧ numLarge δ θ₀ ≤ a ∧ (∀ j, |θ₀ j| ≤ E) ∧
    S.card = a ∧ ∀ j ∉ S, |θ₀ j| ≤ δ

/-- (WG3): `∫_{|t|>δ} π(t) dt ≤ J^{−(1+μ)}`. -/
def WG3 (pdf : ℝ → ℝ) (δ μ : ℝ) (J : ℕ) : Prop :=
  coordPrior pdf {t | δ < |t|} ≤ ENNReal.ofReal ((J : ℝ) ^ (-(1 + μ)))

/-- (WG4), in the equivalent form `Π(∑_{j∉S} |θ_j| ≤ η ε̃) ≥ exp(−c₄ n ε̃²)`. -/
def WG4 (pdf : ℝ → ℝ) (J : ℕ) (S : Finset (Fin J)) (η εt c4 : ℝ) (n : ℕ) : Prop :=
  ENNReal.ofReal (Real.exp (-(c4 * n * εt ^ 2))) ≤
    prior J pdf {θ | ∑ j ∈ Sᶜ, |θ j| ≤ η * εt}

/-- (WG5): some `π_low > 0` bounds the density from below almost everywhere on `[−E, E]`, and
`a [log a + 2 log(1/ε̃) − log π_low]_+ ≤ c₅ n ε̃²`. For `c₅ ≥ 0` the positive part is immaterial
(`wg5_iff_noPos`), and the paper's form, with `π_low = inf_{|t|≤E} π(t)` and no positive part,
implies this one (`wg5Paper_implies_wg5`, in `WG5Bridge.lean`). -/
def WG5 (pdf : ℝ → ℝ) (E εt c5 : ℝ) (a n : ℕ) : Prop :=
  ∃ πlow : ℝ, 0 < πlow ∧ (∀ᵐ t ∂volume, |t| ≤ E → πlow ≤ pdf t) ∧
    (a : ℝ) * max 0 (Real.log a + 2 * Real.log (1 / εt) - Real.log πlow) ≤ c5 * n * εt ^ 2

/-! ## Theorem 1 -/

/-- The two conclusions of Theorem 1 at a fixed `n`:
`E₀ Π(‖f − f₀‖_{2,n} > M ε_n | Y) ≤ 5 e^{−n ε̃²}` and `E₀ Π(N(θ) > A s_n | Y) ≤ 2 e^{−n ε̃²}`. -/
def MasterConclusion (n J : ℕ) (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (pdf : ℝ → ℝ) (εt δ M : ℝ) (a : ℕ) (K η μ c4 c5 : ℝ) : Prop :=
  (∫⁻ y, posterior σ X f₀ (prior J pdf) y (farSet X f₀ (M * epsRate n J a εt)) ∂(dataLaw σ f₀)
      ≤ ENNReal.ofReal (5 * Real.exp (-(n * εt ^ 2)))) ∧
  (∫⁻ y, posterior σ X f₀ (prior J pdf) y
        (denseSet δ (Aconst K η σ μ c4 c5 * sRate n J a εt)) ∂(dataLaw σ f₀)
      ≤ ENNReal.ofReal (2 * Real.exp (-(n * εt ^ 2))))

/-- Hypotheses of Theorem 1 at a fixed sample size `n`: the assumptions at `n`, the standing
requirement `δ ≤ ε̃/J`, and seven explicit numeric conditions (fields `e1`–`e7`). -/
structure MasterHyp (n J : ℕ) (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ)
    (pdf : ℝ → ℝ) (εt δ E M : ℝ) (a : ℕ) (K η μ c4 c5 : ℝ) : Prop where
  hn : 0 < n
  hJ : 2 ≤ J
  hσ : 0 < σ
  hpdf : IsProbDensity pdf
  hεt : 0 < εt
  hδ : 0 < δ
  hE : 0 < E
  ha1 : 1 ≤ a
  haJ : a ≤ J
  hK : 0 < K
  hη : 0 < η
  hμ : 0 < μ
  hc4 : 0 ≤ c4
  hc5 : 0 ≤ c5
  hδεt : δ ≤ εt / J
  basis : BasisBound X K
  approx : ∃ θ₀ S, SparseApprox X f₀ εt δ E a θ₀ S ∧ WG4 pdf J S η εt c4 n
  wg3 : WG3 pdf δ μ J
  wg5 : WG5 pdf E εt c5 a n
  e1 : εt ≤ η
  e2 : 2 ≤ (J : ℝ) ^ μ
  e3 : Real.log 2 ≤ n * εt ^ 2
  e4 : 1 + Real.log 97 ≤ Real.log J
  e5 : 16 * K ≤ M
  e6 : 16 * σ ^ 2 * (2 * (Aconst K η σ μ c4 c5 : ℝ) + 1) ≤ M ^ 2
  e7 : 64 * σ ^ 2 * (C1 K η σ c4 c5 + 1) ≤ M ^ 2

/-- **Theorem 1, non-asymptotic form.** -/
def MasterStatement : Prop :=
  ∀ (n J : ℕ) (σ : ℝ) (X : Matrix (Fin n) (Fin J) ℝ) (f₀ : Fin n → ℝ) (pdf : ℝ → ℝ)
    (εt δ E M : ℝ) (a : ℕ) (K η μ c4 c5 : ℝ),
    MasterHyp n J σ X f₀ pdf εt δ E M a K η μ c4 c5 →
    MasterConclusion n J σ X f₀ pdf εt δ M a K η μ c4 c5

/-- Hypotheses of Theorem 1 as stated in the paper, for sequences indexed by `n`.
Every condition on the sequences is required only for all sufficiently large `n`; the
constants `σ, K, η, μ, c₄, c₅` are fixed. `J_n ≥ 2` eventually follows from `J_n → ∞`. -/
structure AsymptoticHyp (J : ℕ → ℕ) (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ)
    (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ) (pdf : ℕ → ℝ → ℝ) (εt δ E M : ℕ → ℝ) (a : ℕ → ℕ)
    (K η μ c4 c5 : ℝ) : Prop where
  hσ : 0 < σ
  hK : 0 < K
  hη : 0 < η
  hη1 : η < 1
  hμ : 0 < μ
  hc4 : 0 ≤ c4
  hc5 : 0 ≤ c5
  hJ : Tendsto J atTop atTop
  hnεt : Tendsto (fun n : ℕ => (n : ℝ) * εt n ^ 2) atTop atTop
  hs : Tendsto (fun n : ℕ => (sRate n (J n) (a n) (εt n) : ℝ) * Real.log (J n) / n) atTop (𝓝 0)
  hM : Tendsto M atTop atTop
  hpdf : ∀ᶠ n in atTop, IsProbDensity (pdf n)
  hεt : ∀ᶠ n in atTop, 0 < εt n
  hδ : ∀ᶠ n in atTop, 0 < δ n
  hE : ∀ᶠ n in atTop, 0 < E n
  ha : ∀ᶠ n in atTop, 1 ≤ a n ∧ a n ≤ J n
  hδεt : ∀ᶠ n in atTop, δ n ≤ εt n / J n
  hbasis : ∀ᶠ n in atTop, BasisBound (X n) K
  hA2 : ∀ᶠ n in atTop, ∃ θ₀ S, SparseApprox (X n) (f₀ n) (εt n) (δ n) (E n) (a n) θ₀ S ∧
    WG4 (pdf n) (J n) S η (εt n) c4 n
  h3 : ∀ᶠ n in atTop, WG3 (pdf n) (δ n) μ (J n)
  h5 : ∀ᶠ n in atTop, WG5 (pdf n) (E n) (εt n) c5 (a n) n

/-- Conclusions of Theorem 1: for all sufficiently large `n` both bounds of `MasterConclusion`,
and for every `ζ > 0`, `P₀{Π(‖f − f₀‖_{2,n} > M_n ε_n | Y) > ζ} → 0` and
`P₀{Π(N_δ(θ) > A s_n | Y) > ζ} → 0` (convergence in `P₀`-probability). -/
def AsymptoticConclusion (J : ℕ → ℕ) (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ)
    (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ) (pdf : ℕ → ℝ → ℝ) (εt δ M : ℕ → ℝ) (a : ℕ → ℕ)
    (K η μ c4 c5 : ℝ) : Prop :=
  (∀ᶠ n in atTop,
      MasterConclusion n (J n) σ (X n) (f₀ n) (pdf n) (εt n) (δ n) (M n) (a n) K η μ c4 c5) ∧
  (∀ ζ : ℝ, 0 < ζ → Tendsto (fun n : ℕ => dataLaw σ (f₀ n)
      {y | ENNReal.ofReal ζ < posterior σ (X n) (f₀ n) (prior (J n) (pdf n)) y
        (farSet (X n) (f₀ n) (M n * epsRate n (J n) (a n) (εt n)))}) atTop (𝓝 0)) ∧
  (∀ ζ : ℝ, 0 < ζ → Tendsto (fun n : ℕ => dataLaw σ (f₀ n)
      {y | ENNReal.ofReal ζ < posterior σ (X n) (f₀ n) (prior (J n) (pdf n)) y
        (denseSet (δ n) (Aconst K η σ μ c4 c5 * sRate n (J n) (a n) (εt n)))}) atTop (𝓝 0))

/-- **Theorem 1** as stated in the paper. -/
def AsymptoticStatement : Prop :=
  ∀ (J : ℕ → ℕ) (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : ∀ n : ℕ, Fin n → ℝ)
    (σ : ℝ) (pdf : ℕ → ℝ → ℝ) (εt δ E M : ℕ → ℝ) (a : ℕ → ℕ) (K η μ c4 c5 : ℝ),
    AsymptoticHyp J X f₀ σ pdf εt δ E M a K η μ c4 c5 →
    AsymptoticConclusion J X f₀ σ pdf εt δ M a K η μ c4 c5

/-! ## The horseshoe prior -/

/-- Half-Cauchy density `f_{C⁺}(λ) = 2 / (π (1 + λ²))` for `λ > 0`, zero otherwise. -/
def halfCauchyPDF (l : ℝ) : ℝ := if 0 < l then 2 / (Real.pi * (1 + l ^ 2)) else 0

/-- Horseshoe marginal density with global scale `τ`:
`π_τ(t) = ∫₀^∞ φ(t; 0, λ²τ²) f_{C⁺}(λ) dλ`. At `t = 0` the true density is `+∞`; there the
integrand is not integrable and Lean's convention gives the value `0`, which changes the
density on a Lebesgue-null set only. -/
def horseshoePDF (τ : ℝ) (t : ℝ) : ℝ :=
  ∫ l in Set.Ioi (0 : ℝ), gaussianPDFReal 0 (Real.toNNReal (l ^ 2 * τ ^ 2)) t * halfCauchyPDF l

/-- The horseshoe density is a probability density for every `τ > 0`. -/
def HorseshoeDensityStatement : Prop := ∀ τ : ℝ, 0 < τ → IsProbDensity (horseshoePDF τ)

/-- **The horseshoe prior with a deterministic global scale satisfies Assumption 3**
(translation of Wei and Ghosal 2020, Theorem 3.3): if `τ_n ≤ c_τ J_n^{−(2+μ'')} / √n`,
`log(1/τ_n), log(1/ε̃_n), log E_n ≤ B log J_n`, `a_n log J_n ≤ B n ε̃_n²`, and `δ_n ≥ c_δ ε̃_n/J_n`,
then (WG3) holds with `μ = μ''/2`, (WG4) with `c₄ = 1` for every active set of size `a_n`, and
(WG5) with `c₅ = B(6 + 5B)`, for all sufficiently large `n`. -/
def HorseshoeAssumption3Statement : Prop :=
  ∀ (J : ℕ → ℕ) (εt δ E τ : ℕ → ℝ) (a : ℕ → ℕ) (η μ'' cδ cτ B : ℝ),
    Tendsto J atTop atTop → Tendsto (fun n : ℕ => (n : ℝ) * εt n ^ 2) atTop atTop →
    0 < η → 0 < μ'' → 0 < cδ → 0 < cτ → 0 ≤ B →
    (∀ᶠ n in atTop, 1 ≤ a n ∧ a n ≤ J n) →
    (∀ᶠ n in atTop, 0 < εt n) → (∀ᶠ n in atTop, 0 < E n) → (∀ᶠ n in atTop, 0 < τ n) →
    (∀ᶠ n in atTop, cδ * εt n / J n ≤ δ n) →
    (∀ᶠ n in atTop, τ n ≤ cτ * (J n : ℝ) ^ (-(2 + μ'')) / Real.sqrt n) →
    (∀ᶠ n in atTop, (a n : ℝ) * Real.log (J n) ≤ B * n * εt n ^ 2 ∧
        Real.log (1 / εt n) ≤ B * Real.log (J n) ∧
        Real.log (1 / τ n) ≤ B * Real.log (J n) ∧
        Real.log (E n) ≤ B * Real.log (J n)) →
    ∀ᶠ n in atTop,
      WG3 (horseshoePDF (τ n)) (δ n) (μ'' / 2) (J n) ∧
      (∀ S : Finset (Fin (J n)), S.card = a n → WG4 (horseshoePDF (τ n)) (J n) S η (εt n) 1 n) ∧
      WG5 (horseshoePDF (τ n)) (E n) (εt n) (B * (6 + 5 * B)) (a n) n

/-! ## Dictionaries -/

/-- Design matrix of a dictionary `ξ` at design points `x`: `X i j = ξ_j(x_i)`. -/
def designMatrix {n J : ℕ} {𝒳 : Type*} (ξ : Fin J → 𝒳 → ℝ) (x : Fin n → 𝒳) :
    Matrix (Fin n) (Fin J) ℝ :=
  Matrix.of fun i j => ξ j (x i)

/-- Real trigonometric atoms on `[0,1]`: `ψ₀ = 1`, `ψ_{2j−1}(x) = √2 cos(2πjx)`,
`ψ_{2j}(x) = √2 sin(2πjx)`. -/
def fourierAtom (ν : ℕ) (x : ℝ) : ℝ :=
  if ν = 0 then 1
  else if ν % 2 = 1 then Real.sqrt 2 * Real.cos (2 * Real.pi * ((ν + 1) / 2 : ℕ) * x)
  else Real.sqrt 2 * Real.sin (2 * Real.pi * (ν / 2 : ℕ) * x)

/-- Tensor Fourier atom on `[0,1]^d`: `Ψ_ν(x) = ∏_k ψ_{ν_k}(x_k)`. -/
def fourierTensor {d : ℕ} (ν : Fin d → ℕ) (x : Fin d → ℝ) : ℝ := ∏ k, fourierAtom (ν k) (x k)

/-- Assumption 1 for every Fourier dictionary (any finite family of tensor atoms, any design),
with `K = 2^{d/2}`. -/
def FourierBasisStatement : Prop :=
  ∀ (n J d : ℕ) (idx : Fin J → Fin d → ℕ) (x : Fin n → Fin d → ℝ),
    BasisBound (designMatrix (fun j => fourierTensor (idx j)) x) (Real.sqrt 2 ^ d)

/-- Clamped uniform knot vector of order `q` with `K` subintervals of `[0,1]`:
`t_i = 0` for `i ≤ q − 1`, `t_i = (i − q + 1)/K` for `q − 1 ≤ i ≤ K + q − 1`,
`t_i = 1` for `i ≥ K + q − 1`. -/
def knot (q K : ℕ) (i : ℕ) : ℝ := max 0 (min 1 (((i : ℝ) - ((q : ℝ) - 1)) / K))

/-- Cox–de Boor recursion on the knots `knot q K`: `bspl q K k i` is the B-spline of order `k`
(degree `k − 1`) starting at knot `i`. Order 1 is the indicator of `[t_i, t_{i+1})`, with the
last nondegenerate interval closed at `1`. Divisions by zero give `0` (Lean's convention), which
is the usual B-spline convention for repeated knots. -/
def bspl (q K : ℕ) : ℕ → ℕ → ℝ → ℝ
  | 0, _, _ => 0
  | 1, i, x =>
      if (knot q K i ≤ x ∧ x < knot q K (i + 1)) ∨
          (x = 1 ∧ knot q K i < 1 ∧ knot q K (i + 1) = 1) then 1 else 0
  | k + 2, i, x =>
      (x - knot q K i) / (knot q K (i + k + 1) - knot q K i) * bspl q K (k + 1) i x +
        (knot q K (i + k + 2) - x) / (knot q K (i + k + 2) - knot q K (i + 1)) *
          bspl q K (k + 1) (i + 1) x

/-- The order-`q` B-spline basis on `[0,1]` with `K` equal subintervals:
`B_i = bspl q K q i`, `i = 0, …, K + q − 2`. -/
def bspline (q K i : ℕ) (x : ℝ) : ℝ := bspl q K q i x

/-- Tensor-product B-spline atom on `[0,1]^d` with per-coordinate order, number of
subintervals, and index. A multiresolution union is a family of such atoms with different `K`. -/
def bsplineTensor {d : ℕ} (q K i : Fin d → ℕ) (x : Fin d → ℝ) : ℝ :=
  ∏ k, bspline (q k) (K k) (i k) (x k)

/-- Assumption 1 for every B-spline dictionary: any finite family of tensor B-spline atoms
(any orders `≥ 1`, any numbers of subintervals `≥ 1`, any indices, hence any multiresolution
union) with design points in `[0,1]^d` satisfies Assumption 1 with `K = 1`. -/
def BSplineBasisStatement : Prop :=
  ∀ (n J d : ℕ) (q K i : Fin J → Fin d → ℕ) (x : Fin n → Fin d → ℝ),
    (∀ j k, 1 ≤ q j k) → (∀ j k, 1 ≤ K j k) → (∀ m k, x m k ∈ Set.Icc (0 : ℝ) 1) →
    BasisBound (designMatrix (fun j => bsplineTensor (q j) (K j) (i j)) x) 1

/-- Hypotheses of Theorem 1 for the horseshoe prior: those of `AsymptoticHyp` except
(WG3)–(WG5) and the density, replaced by the hypotheses of `HorseshoeAssumption3Statement`. -/
structure MainHorseshoeHyp (J : ℕ → ℕ) (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ)
    (f₀ : ∀ n : ℕ, Fin n → ℝ) (σ : ℝ) (τ εt δ E M : ℕ → ℝ) (a : ℕ → ℕ)
    (K η μ'' cδ cτ B : ℝ) : Prop where
  hσ : 0 < σ
  hK : 0 < K
  hη : 0 < η
  hη1 : η < 1
  hμ'' : 0 < μ''
  hcδ : 0 < cδ
  hcτ : 0 < cτ
  hB : 0 ≤ B
  hJ : Tendsto J atTop atTop
  hnεt : Tendsto (fun n : ℕ => (n : ℝ) * εt n ^ 2) atTop atTop
  hs : Tendsto (fun n : ℕ => (sRate n (J n) (a n) (εt n) : ℝ) * Real.log (J n) / n) atTop (𝓝 0)
  hM : Tendsto M atTop atTop
  hτ : ∀ᶠ n in atTop, 0 < τ n
  hεt : ∀ᶠ n in atTop, 0 < εt n
  hδ : ∀ᶠ n in atTop, 0 < δ n
  hE : ∀ᶠ n in atTop, 0 < E n
  ha : ∀ᶠ n in atTop, 1 ≤ a n ∧ a n ≤ J n
  hδεt : ∀ᶠ n in atTop, δ n ≤ εt n / J n
  hbasis : ∀ᶠ n in atTop, BasisBound (X n) K
  hA2 : ∀ᶠ n in atTop, ∃ θ₀ S, SparseApprox (X n) (f₀ n) (εt n) (δ n) (E n) (a n) θ₀ S
  hcδev : ∀ᶠ n in atTop, cδ * εt n / J n ≤ δ n
  hτev : ∀ᶠ n in atTop, τ n ≤ cτ * (J n : ℝ) ^ (-(2 + μ'')) / Real.sqrt n
  hbudget : ∀ᶠ n in atTop, (a n : ℝ) * Real.log (J n) ≤ B * n * εt n ^ 2 ∧
    Real.log (1 / εt n) ≤ B * Real.log (J n) ∧
    Real.log (1 / τ n) ≤ B * Real.log (J n) ∧
    Real.log (E n) ≤ B * Real.log (J n)

/-- **Theorem 1 for the horseshoe prior**: Theorem 1 with
`π_n = horseshoePDF τ_n`; the constants are `μ = μ''/2`, `c₄ = 1`, `c₅ = B(6 + 5B)`. -/
def MainHorseshoeStatement : Prop :=
  ∀ (J : ℕ → ℕ) (X : ∀ n : ℕ, Matrix (Fin n) (Fin (J n)) ℝ) (f₀ : ∀ n : ℕ, Fin n → ℝ)
    (σ : ℝ) (τ εt δ E M : ℕ → ℝ) (a : ℕ → ℕ) (K η μ'' cδ cτ B : ℝ),
    MainHorseshoeHyp J X f₀ σ τ εt δ E M a K η μ'' cδ cτ B →
    AsymptoticConclusion J X f₀ σ (fun n => horseshoePDF (τ n)) εt δ M a K η (μ'' / 2) 1
      (B * (6 + 5 * B))

end LargePrior
