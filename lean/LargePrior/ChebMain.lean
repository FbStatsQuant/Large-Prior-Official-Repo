import LargePrior.ChebEndToEnd
import LargePrior.ChebTransferHigh

/-!
# Chebyshev dictionary: premise-free headline theorems (milestone MS2)

`ChebProfile` and `ChebEndToEnd` prove the profile lemmas and Corollary 1 for the tensor
Chebyshev dictionary conditionally on `ChebTransferStatement`. `ChebTransferHigh` proves that
statement (`cheb_transfer_statement`). This module discharges the transfer premise, so every
theorem below has a frozen `ChebSpec` statement as its type with no extra premise (`JacksonIneq`
remains an explicit hypothesis inside those statements).

* `chebyshev_profile`: Lemma `chebyshev-profile` (D:514–531).
* `chebyshev_aniso_profile`: Lemma `chebyshev-aniso-profile` (D:601–622).
* `chebyshev_profile_at`: the empirical-norm `ProfileAt` form used by Corollary 1.
* `cor_chebyshev`: Corollary 1 (S:143–204) for the anisotropic tensor Chebyshev dictionary,
  explicit constants `C_sp = 1`, `E = R`, any `C_ε ≥ d · C_app`. Like the shipped
  `cor_horseshoe`, it is specialised to the horseshoe prior with scale `corTau` and `μ = μ''/2`.
  It is the anisotropic corollary that PLAN §7 calls `cor_chebyshev_aniso`.
* `cor_chebyshev_ex`: the same with existential constants and ceiling sizes, shaped like
  `CorFourierStatement`.

`chebyshev_basis` (`ChebBasis`), `cheb_transfer_statement` (`ChebTransferHigh`) and
`cor_chebyshev_holder` (`ChebEndToEnd`) are premise-free where they are proved.
-/

namespace LargePrior

theorem chebyshev_profile : ChebyshevProfileStatement :=
  chebyshev_profile_of cheb_transfer_statement

theorem chebyshev_aniso_profile : ChebyshevAnisoProfileStatement :=
  chebyshev_aniso_profile_of cheb_transfer_statement

theorem chebyshev_profile_at : ChebyshevProfileAtStatement :=
  chebyshev_profile_at_of cheb_transfer_statement

theorem cor_chebyshev : CorChebyshevStatement :=
  cor_chebyshev_of cheb_transfer_statement

theorem cor_chebyshev_ex : CorChebyshevExStatement :=
  cor_chebyshev_ex_of cheb_transfer_statement

end LargePrior
