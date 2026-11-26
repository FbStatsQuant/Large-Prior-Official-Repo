import LargePrior
open LargePrior

/-! Each main result has exactly its `Spec.lean` type and depends only on the standard axioms. -/

example : MasterStatement := master_theorem
example : AsymptoticStatement := asymptotic_theorem
example : MainHorseshoeStatement := main_horseshoe
example : HorseshoeDensityStatement := horseshoe_isProbDensity
example : HorseshoeAssumption3Statement := horseshoe_assumption3
example : FourierBasisStatement := fourier_basis
example : BSplineBasisStatement := bspline_basis

#print axioms master_theorem
#print axioms asymptotic_theorem
#print axioms main_horseshoe
#print axioms horseshoe_isProbDensity
#print axioms horseshoe_assumption3
#print axioms fourier_basis
#print axioms bspline_basis
#print axioms nonvacuity
#print axioms nonvacuity_conclusion
#print axioms posterior_ref_invariant

/-! Corollary 1 and the sparse approximation lemmas. -/

example : CorollaryStatement := corollary_main
example : CorHorseshoeStatement := cor_horseshoe
example : FourierProfileStatement := fourier_profile
example : BSplineProfileStatement := bspline_profile
example : BSplineProfileCubeStatement := bspline_profile_cube
example : CorFourierStatement := cor_fourier
example : CorBSplineStatement := cor_bspline
example : CorBSplineCubeStatement := cor_bspline_cube
example : CorHolderStatement := cor_holder
example : CorTheorem1InputsStatement := cor_asymptoticHyp

#print axioms corollary_main
#print axioms cor_horseshoe
#print axioms fourier_profile
#print axioms bspline_profile
#print axioms bspline_profile_cube
#print axioms cor_fourier
#print axioms cor_bspline
#print axioms cor_bspline_cube
#print axioms cor_holder
#print axioms corHyp_nonvacuity
#print axioms corHorseshoe_nonvacuity
#print axioms corFourier_nonvacuity
#print axioms corBSpline_instance_conclusion
#print axioms corHolder_id_conclusion
#print axioms jackson_lip
#print axioms corFourierHalf_nonvacuity
#print axioms corFourier_instance_conclusion

/-! Theorem 1 inputs, permutation invariance, and the paper's (WG5). -/

#print axioms cor_asymptoticHyp
#print axioms wg4_of_card_eq
#print axioms wg5_iff_noPos
#print axioms wg5Paper_implies_wg5

/-! The paper's horseshoe paragraph. -/

example : HorseshoeAssumption3MuStatement := horseshoe_assumption3_mu
example : HorseshoePaperConditionsStatement := horseshoe_paper_conditions
example : HorseshoeAssumption3Statement := horseshoe_assumption3_of_mu

#print axioms horseshoe_assumption3_mu
#print axioms horseshoe_paper_conditions
#print axioms horseshoe_assumption3_of_mu

/-! The tensor Chebyshev dictionary.
`cor_chebyshev` is the anisotropic Corollary 1. -/

example : ChebyshevBasisStatement := chebyshev_basis
example : ChebTransferStatement := cheb_transfer_statement
example : ChebyshevProfileStatement := chebyshev_profile
example : ChebyshevAnisoProfileStatement := chebyshev_aniso_profile
example : ChebyshevProfileAtStatement := chebyshev_profile_at
example : CorChebyshevStatement := cor_chebyshev
example : CorChebyshevExStatement := cor_chebyshev_ex
example : CorChebyshevHolderStatement := cor_chebyshev_holder
example : ChebSanityHolder := cheb_sanity_holder
example : ChebSanityCtr := cheb_sanity_ctr
example : ChebSanityAnisoUniv := cheb_sanity_aniso_univ

#print axioms chebyshev_basis
#print axioms cheb_transfer
#print axioms cheb_transfer_statement
#print axioms chebyshev_profile
#print axioms chebyshev_aniso_profile
#print axioms chebyshev_profile_at
#print axioms cor_chebyshev
#print axioms cor_chebyshev_ex
#print axioms cor_chebyshev_holder
#print axioms cheb_sanity_holder
#print axioms cheb_sanity_ctr
#print axioms cheb_sanity_aniso_univ
#print axioms cheb_witness_sq
#print axioms cheb_witness_sq_transfer
#print axioms chebCtr_two_three
#print axioms cheb_witness_sq_mul
#print axioms cor_chebyshev_witness_two
#print axioms cor_chebyshev_witness_one
