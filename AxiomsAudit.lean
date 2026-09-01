import TermCodingDispersion

/-!
Declaration-level axiom report for the Paper 2 formalisation, updated for V10.

Every `#print axioms` line below must report a subset of
`[propext, Classical.choice, Quot.sound]`.  The Paper 1 headline
declarations are kept (unchanged) at the end of the file.
-/

-- ## Paper 2: dispersion instances and decision problems
#print axioms TermCoding.Dispersion.disp_eq_pow_iff
#print axioms TermCoding.Dispersion.disp_congr_equiv
#print axioms TermCoding.Dispersion.dispN_mono
#print axioms TermCoding.Dispersion.perfectDisp_iff_surjectiveWitness
#print axioms TermCoding.Dispersion.bij_iff_fin

-- ## lem:diamond-not-bij and the diamond gadget
#print axioms TermCoding.Dispersion.diamond_not_injective
#print axioms TermCoding.Dispersion.diamond_not_surjective
#print axioms TermCoding.Dispersion.diamond_not_perfect
#print axioms TermCoding.Dispersion.diversifiedDiamond_bijective
#print axioms TermCoding.Dispersion.pow_le_dispN_diamond
#print axioms TermCoding.Dispersion.div_pow_le_dispN_diamond

-- ## lem:disp-embed (exact match with Paper 1)
#print axioms TermCoding.Dispersion.termMap_eq_paper1
#print axioms TermCoding.Dispersion.disp_eq_dispersionMax
#print axioms TermCoding.Dispersion.dispN_eq_codingTheoryMax

-- ## lem:square-perfect-equals-bij, cor:bij-reduces-perfect, rem:inverse-extension
#print axioms TermCoding.Dispersion.perfectDisp_iff_bij
#print axioms TermCoding.Dispersion.square_tfae
#print axioms TermCoding.Dispersion.identity_reduction
#print axioms TermCoding.Dispersion.bijective_of_inverseEquations
#print axioms TermCoding.Dispersion.exists_inverseExtension_of_bijective
#print axioms TermCoding.Dispersion.exists_inverseExtension_iff

-- ## lem:product-surjectivity, thm:perfect-spectrum-structure(i), lem:direct-power
#print axioms TermCoding.Dispersion.eval_productInterp
#print axioms TermCoding.Dispersion.termMap_productInterp
#print axioms TermCoding.Dispersion.surjective_productInterp
#print axioms TermCoding.Dispersion.dispN_mul_eq_of_perfect
#print axioms TermCoding.Dispersion.eval_powerInterp
#print axioms TermCoding.Dispersion.termMap_powerInterp_eq
#print axioms TermCoding.Dispersion.surjective_powerInterp
#print axioms TermCoding.Dispersion.dispN_pow_eq_of_perfect

-- ## def:perfect-spectrum, thm:perfect-spectrum-structure (spectrum level)
#print axioms TermCoding.Dispersion.perfectSpectrum_nonempty_iff
#print axioms TermCoding.Dispersion.mul_mem_perfectSpectrum
#print axioms TermCoding.Dispersion.pow_mem_perfectSpectrum
#print axioms TermCoding.Dispersion.exponent_eq_of_spectrum_nonempty
#print axioms TermCoding.Dispersion.mem_perfectSpectrum_square_iff
#print axioms TermCoding.Dispersion.perfectDisp_two_iff_bij_two

-- ## thm:one-output, cor:bij-one, thm:landscape(ii)
#print axioms TermCoding.Dispersion.mem_perfectSpectrum_single_iff
#print axioms TermCoding.Dispersion.perfectSpectrum_single_of_hasVar
#print axioms TermCoding.Dispersion.perfectSpectrum_single_of_ground
#print axioms TermCoding.Dispersion.perfectSpectrum_single_dichotomy

-- ## prop:small-spectra (least alphabet sizes 3 and 4, with power sets)
#print axioms TermCoding.Dispersion.sigma_no_interpretation_three
#print axioms TermCoding.Dispersion.perfectSpectrum_tau_least
#print axioms TermCoding.Dispersion.pow_three_mem_perfectSpectrum_tau
#print axioms TermCoding.Dispersion.perfectSpectrum_sigma_least
#print axioms TermCoding.Dispersion.pow_four_mem_perfectSpectrum_sigma

-- ## thm:perfect-implies-full-rate (unconditional) and the exponent
#print axioms TermCoding.Dispersion.dispRate_tendsto
#print axioms TermCoding.Dispersion.limit_eq_of_perfect
#print axioms TermCoding.Dispersion.exponent_eq_of_perfect
#print axioms TermCoding.Dispersion.fullRateDisp_of_perfectDisp
#print axioms TermCoding.Dispersion.exponentData_diamond
#print axioms TermCoding.Dispersion.exponent_diamond
#print axioms TermCoding.Dispersion.not_perfect_of_fullRate_fails

-- ## lem:padding-outputs, lem:unused-inputs
#print axioms TermCoding.Dispersion.padMap_surjective_iff
#print axioms TermCoding.Dispersion.padMap_not_surjective_empty
#print axioms TermCoding.Dispersion.restrictMap_surjective_iff

-- ## thm:reduction-kk, thm:reduction-nr
#print axioms TermCoding.Dispersion.termMap_padInstance
#print axioms TermCoding.Dispersion.perfectDisp_padInstance_iff
#print axioms TermCoding.Dispersion.size_padInstance
#print axioms TermCoding.Dispersion.reduction_kk
#print axioms TermCoding.Dispersion.reduction_nr

-- ## r = 1 remark and BIJ_1
#print axioms TermCoding.Dispersion.prescription_consistent
#print axioms TermCoding.Dispersion.eval_routingInterp_slice
#print axioms TermCoding.Dispersion.perfectDisp_single_iff
#print axioms TermCoding.Dispersion.bij_one_iff
#print axioms TermCoding.Dispersion.bijective_single_of_hasVar

-- ## Term-cuts (Riis–Gadouleau 2019, Definition 2 / Lemma 3)
#print axioms TermCoding.Dispersion.imageCard_le_pow_card_of_termCut
#print axioms TermCoding.Dispersion.disp_le_pow_termCutNumber
#print axioms TermCoding.Dispersion.termCutNumber_diamond

-- ## Dynamic routing (Riis–Gadouleau 2019, Definition 9 / Lemma 4) and weak duality
#print axioms TermCoding.Dispersion.eval_routing
#print axioms TermCoding.Dispersion.pathSystem_pow_le_dispN
#print axioms TermCoding.Dispersion.pathSystem_lowerBound_real
#print axioms TermCoding.Dispersion.pathSystem_card_le_termCutNumber
#print axioms TermCoding.Dispersion.diamondPathSystem
#print axioms TermCoding.Dispersion.mengerForTerms_diamond
#print axioms TermCoding.Dispersion.maxFlowLowerBound_of_pathSystem
#print axioms TermCoding.Dispersion.maxFlowLowerBound_of_menger

-- ## thm:ptime-threshold, analytic layer
#print axioms TermCoding.Dispersion.thresholdConditions_pow_add_one
#print axioms TermCoding.Dispersion.threshold_iff
#print axioms TermCoding.Dispersion.decideThreshold_correct
#print axioms TermCoding.Dispersion.rate_tendsto

-- ## prop:scalar-det-criterion-main and consequences
#print axioms TermCoding.Dispersion.eval_scalarLinearInterp
#print axioms TermCoding.Dispersion.bijective_scalarLinear_iff
#print axioms TermCoding.Dispersion.scalarLinearWitness_iff
#print axioms TermCoding.Dispersion.exists_primeField_witness_iff
#print axioms TermCoding.Dispersion.exists_finiteField_witness_iff
#print axioms TermCoding.Dispersion.exists_galoisField_witness_iff

-- ## Paper 1 bridge (V6 Sections 3–4) and counterexamples
#print axioms TermCoding.Dispersion.diversification_le
#print axioms TermCoding.Dispersion.solutions_eq_winning
#print axioms TermCoding.Dispersion.sandwich_upper
#print axioms TermCoding.Dispersion.sandwich_lower
#print axioms TermCoding.Dispersion.sandwich_limsup
#print axioms TermCoding.Dispersion.onePassQuotient_not_leftFunctional
#print axioms TermCoding.Dispersion.fnfRemark_quotient_not_outputFunctional
#print axioms TermCoding.Dispersion.fnfRemark_paper1_repair
#print axioms TermCoding.Dispersion.card_subterms_doublingTerm
#print axioms TermCoding.Dispersion.size_doublingTerm

-- ## Degenerate cases and experiments
#print axioms TermCoding.Dispersion.perfectDisp_of_r_zero
#print axioms TermCoding.Dispersion.not_perfectDisp_of_k_zero
#print axioms TermCoding.Dispersion.perfectDispAt_one
#print axioms TermCoding.Dispersion.tau_no_witness_two
#print axioms TermCoding.Dispersion.sigma_no_witness_two
#print axioms TermCoding.Dispersion.tau_witness_three
#print axioms TermCoding.Dispersion.sigma_witness_four
#print axioms TermCoding.Dispersion.sigma_no_witness_three
#print axioms TermCoding.Dispersion.sigma_bijectivity_spectrum_low

-- ## Landscape
#print axioms TermCoding.Dispersion.landscape_square
#print axioms TermCoding.Dispersion.landscape_reduction
#print axioms TermCoding.Dispersion.landscape_rate

-- ## Conditional layer (explicit hypothesis `MaxFlowLowerBound`; no axiom)
#print axioms TermCoding.Dispersion.exponentData_of_lowerBound
#print axioms TermCoding.Dispersion.exponent_le_termCutNumber
#print axioms TermCoding.Dispersion.exponent_eq_termCutNumber
#print axioms TermCoding.Dispersion.threshold_iff_of_lowerBound
#print axioms TermCoding.Dispersion.fullRate_iff_termCutNumber
#print axioms TermCoding.Dispersion.fullRate_iff_eventual
#print axioms TermCoding.Dispersion.perfect_implies_termCutNumber_eq
#print axioms TermCoding.Dispersion.maxFlowLowerBound_diamond

-- ## Paper 1 headline declarations (reused, unchanged)
#print axioms TermCoding.Normalisation.system_noCollision
#print axioms TermCoding.Normalisation.solutionsEquiv
#print axioms TermCoding.TermSystem.explicitEqualitiesSolutionsEquiv
#print axioms TermCoding.TermSystem.collisionFreeSolutionsEquiv
#print axioms TermCoding.TermSystem.collisionFreeSystem_noCollision
#print axioms TermCoding.TermSystem.completionSolutionsEquiv
#print axioms TermCoding.TermSystem.diversifiedMaxSolutionCount_eq_ordinaryWinningMax_of_outputFunctional
#print axioms TermCoding.TermSystem.finiteSandwich_fintype
#print axioms TermCoding.TermSystem.maxSolutionRate_tendsto
#print axioms TermCoding.TermTheory.maxSolutionRate_tendsto
#print axioms TermCoding.Examples.Dispersion.codingTheoryMax_eq_dispersionMax
