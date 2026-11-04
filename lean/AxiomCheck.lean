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

/-! Corollary 1 and the sparse approximation lemmas (corollary run; statements frozen as cor_v2 on 2026-11-03). -/

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

/-! cor_v2 additions (2026-11-03): W4 export, W7 permutation invariance, W3 (WG5) bridge. -/

#print axioms cor_asymptoticHyp
#print axioms wg4_of_card_eq
#print axioms wg5_iff_noPos
#print axioms wg5Paper_implies_wg5

/-! v3 additions (2026-11-03): the paper's horseshoe paragraph (W1, W5). -/

example : HorseshoeAssumption3MuStatement := horseshoe_assumption3_mu
example : HorseshoePaperConditionsStatement := horseshoe_paper_conditions
example : HorseshoeAssumption3Statement := horseshoe_assumption3_of_mu

#print axioms horseshoe_assumption3_mu
#print axioms horseshoe_paper_conditions
#print axioms horseshoe_assumption3_of_mu
