# Attribution

Each declaration below adapts or closely follows, in whole or in part and with changes, a definition, statement or proof from Mathlib (Apache License, Version 2.0). Names may omit a namespace. Mathlib names and files are those of commit 56a005855ea17e0b0958f73ec801ae140b0a1679 (the names also occur, in the same files, at 0df444a360eaa60ab8c11dca51a86af692955474).

| file | declaration | Mathlib declaration | Mathlib file |
|---|---|---|---|
| `src/Lib/Adelic/Adeles/Basic.lean` | `DenseRange.eq` | `DenseRange.equalizer` | `Mathlib/Topology/DenseEmbedding.lean` |
| `src/Lib/Adelic/Adeles/IdeleModulus.lean` | `New.adeleNorm_algebraMap` | `Subalgebra.LinearDisjoint.norm_algebraMap`, `Subalgebra.LinearDisjoint.leftMulMatrix_basisOfBasisRight_algebraMap` | `Mathlib/RingTheory/LinearDisjoint.lean` |
| `src/Lib/Adelic/Adeles/StrongApproximation.lean` | `New.one_le_prod_norm_Φ` | `NumberField.InfinitePlace.one_le_of_lt_one` | `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean` |
| `src/Lib/Adelic/Hecke/Basic.lean` | `New.levelSpace` | `Representation.invariants` | `Mathlib/RepresentationTheory/Invariants.lean` |
| `src/Lib/Adelic/QuotientMeasure/Basic.lean` | `New.hasCutoff_of_proper` | `MeasureTheory.exists_pos_measure_of_cover`, `SigmaCompactSpace.exists_compact_covering` | `Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean`, `Mathlib/Topology/Compactness/SigmaCompact.lean` |
| `src/Lib/Adelic/QuotientMeasure/MovingTheQuotient.lean` | `New.integrable_mul_comp_inv_mul` | `MeasureTheory.measurePreserving_prod_mul` | `Mathlib/MeasureTheory/Group/Prod.lean` |
| `src/Lib/Adelic/Reduction/MinkowskiTheorems.lean` | `exists_min_of_finite_le` | `Northcott.exists_min_image` | `Mathlib/Order/Northcott.lean` |
| `src/Lib/Adelic/TraceFormula/LineCount.lean` | `New.KeepsLine.rootMultiplicity_charpoly` | `Matrix.charmatrix_toSquareBlock` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` |
| `src/Lib/Adelic/TraceFormula/LineDeterminant.lean` | `New.trace_pow_mul_eq_sum` | `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero` | `Mathlib/Algebra/DirectSum/LinearMap.lean` |
| `src/Lib/Adelic/TraceFormula/LineDeterminant.lean` | `New.trace_restrictGenEigenspace_mul` | `LinearMap.trace_comp_eq_zero_of_commute_of_trace_restrict_eq_zero` | `Mathlib/Algebra/DirectSum/LinearMap.lean` |
| `src/Lib/Adelic/TraceFormula/TestFunction.lean` | `New.exists_eq_pow_of_monic_of_map_eq_pow` | `Polynomial.Monic.irreducible_iff_irreducible_map_fraction_map` | `Mathlib/RingTheory/Polynomial/GaussLemma.lean` |
| `src/Lib/Adelic/TraceFormula/TestFunction.lean` | `TestFunction.translate` | `Representation.coind` | `Mathlib/RepresentationTheory/Coinduced.lean` |
| `src/Lib/Analytic/EntireLFunction.lean` | `New.LSeriesHasSum_mul_vonMangoldt` | `ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux` | `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` |
| `src/Lib/Analytic/EntireLFunction.lean` | `New.entireL_ne_zero` | `DirichletCharacter.continuousOn_neg_logDeriv_LFunctionTrivChar₁` | `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` |
| `src/Lib/Analytic/EntireLFunction.lean` | `New.tendsto_sub_mul_logDeriv_entireL_analyticOrderNatAt` | `AnalyticAt.tendsto_mul_logDeriv_simple_zero` | `Mathlib/Analysis/Calculus/LogDeriv.lean` |
| `src/Lib/Analytic/PolyaVinogradov.lean` | `New.filter_dvd_Ioc_eq_image_mul` | `Int.Ioc_filter_dvd_eq` | `Mathlib/Data/Int/CardIntervalMod.lean` |
| `src/Lib/Analytic/PrimeNumberTheorem/LFunctionGrowth.lean` | `norm_regularL_le_linear` | `LSeries_tendsto_sub_mul_nhds_one_of_tendsto_sum_div_aux₃` | `Mathlib/NumberTheory/LSeries/SumCoeff.lean` |
| `src/Lib/Analytic/Primes.lean` | `New.hasSum_residueClass_one` | `ArithmeticFunction.vonMangoldt.residueClass_eq`, `ArithmeticFunction.vonMangoldt.LSeries_residueClass_eq` | `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` |
| `src/Lib/Analytic/ZeroSymmetry.lean` | `New.prod_euler_factor_ne_zero` | `DirichletCharacter.LFunction_changeLevel` | `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` |
| `src/Lib/CM/Integrality/LogTheta.lean` | `New.CMLattice.subst_mem_multiSeriesRing` | `PowerSeries.subst_toMvPowerSeries` | `Mathlib/RingTheory/MvPowerSeries/Equiv.lean` |
| `src/Lib/CM/KroneckerLimit.lean` | `New.summable_norm_mul_add_rpow` | `EisensteinSeries.summable_norm_eisSummand` | `Mathlib/NumberTheory/ModularForms/EisensteinSeries/IsBoundedAtImInfty.lean` |
| `src/Lib/CM/Sigma/Basic.lean` | `New.exists_eq_zero_of_weight_twelve_of_tendsto_one` | `CuspForm.discriminantEquiv` | `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean` |
| `src/Lib/ClassField/GaloisCohomology/ContinuousCocycles.lean` | `New.DiscreteModule.quotient` | `Submodule.continuousSMul_quotient` | `Mathlib/Topology/Algebra/Module/Basic.lean` |
| `src/Lib/ClassField/Global/AlbertBrauerHasseNoether.lean` | `New.albert_brauer_hasse_noether` | `IsTopologicalGroup.exist_openNormalSubgroup_sub_clopen_nhds_of_one` | `Mathlib/Topology/Algebra/ClopenNhdofOne.lean` |
| `src/Lib/ClassField/Global/ArtinReciprocity.lean` | `New.exists_prime_dvd_orderOf` | `Nat.exists_prime_gt_modEq_one` | `Mathlib/NumberTheory/PrimesCongruentOne.lean` |
| `src/Lib/ClassField/GreenbergWiles/SplitPrimeReciprocity.lean` | `out_inv_mul_mul_out_mem` | `QuotientGroup.out_conj_pow_minimalPeriod_mem` | `Mathlib/GroupTheory/GroupAction/Quotient.lean` |
| `src/Lib/ClassField/Grunwald.lean` | `New.exists_mem_ker_cyclotomicCharMod_smul_ne_of_forall_pow_ne` | `X_pow_sub_C_irreducible_of_prime` | `Mathlib/FieldTheory/KummerPolynomial.lean` |
| `src/Lib/ClassField/Grunwald.lean` | `New.range_intTrace_stepField_eq_top` | `pow_sub_one_dvd_differentIdeal_aux`, `dvd_differentIdeal_of_not_isSeparable` | `Mathlib/RingTheory/DedekindDomain/Different.lean` |
| `src/Lib/ClassField/HeckeL/EulerProduct.lean` | `New.ncard_primesOver_le_finrank` | `Ideal.card_primesOverFinset_le_finrank` | `Mathlib/NumberTheory/RamificationInertia/Basic.lean` |
| `src/Lib/ClassField/Places/DecompositionCyclotomic.lean` | `New.cyclotomicCharMod_eq_of_isPrimitiveRoot` | `IsPrimitiveRoot.autToPow_eq_modularCyclotomicCharacter` | `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean` |
| `src/Lib/ClassField/Places/ValuationSubrings.lean` | `New.FinPlace.ncard_mul_ramificationIdx_mul_inertiaDeg` | `Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn` | `Mathlib/NumberTheory/RamificationInertia/Galois.lean` |
| `src/Lib/Cohomology/Etale/Basic.lean` | `New.Variety.H.dimension_shift_induction` | `CategoryTheory.hasExt_of_enoughInjectives` | `Mathlib/Algebra/Homology/DerivedCategory/Ext/EnoughInjectives.lean` |
| `src/Lib/Cohomology/Etale/Basic.lean` | `homReprEquiv` | `CategoryTheory.uliftCoyonedaEquiv` | `Mathlib/CategoryTheory/Yoneda.lean` |
| `src/Lib/Cohomology/Etale/Basic.lean` | `restrictAlg` | `Algebra.restrictScalars`, `Algebra.compHom` | `Mathlib/Algebra/Algebra/RestrictScalars.lean`, `Mathlib/Algebra/Algebra/Defs.lean` |
| `src/Lib/Cohomology/Etale/DenseSubfunctors.lean` | `New.Variety.mayer_vietoris_shortExact` | `CategoryTheory.CommSq.shortComplex` | `Mathlib/Algebra/Homology/CommSq.lean` |
| `src/Lib/Cohomology/Hodge/Site.lean` | `New.Variety.exteriorMap_iotaMulti` | `ExteriorAlgebra.map_apply_ιMulti` | `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean` |
| `src/Lib/Cohomology/PointClass/NoetherNormalization.lean` | `New.Variety.CutsOutLocus.isIntegralElem_of_valuationSubring` | `Subring.eq_iInf_of_isIntegrallyClosedIn`, `iInf_valuationSubring_superset` | `Mathlib/RingTheory/Valuation/LocalSubring.lean` |
| `src/Lib/Cohomology/ProperBaseChange/SubringSplitting.lean` | `New.Variety.absIntegrallyClosedSubrings.exists_valuationSubring_mem_range_comap` | `Ideal.image_subset_nonunits_valuationSubring` | `Mathlib/RingTheory/Valuation/LocalSubring.lean` |
| `src/Lib/Cyclotomic/Stickelberger.lean` | `New.OddPart.isOfFinOrder_of_norm_eq_one` | `Polynomial.pow_eq_one_of_mahlerMeasure_eq_one` | `Mathlib/NumberTheory/MahlerMeasure.lean` |
| `src/Lib/Cyclotomic/Voronoi.lean` | `New.OddPart.exists_isStickelbergerBound` | `Matrix.det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors` | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` |
| `src/Lib/DiscreteSeries/FlenstedJensen/SquareIntegrability.lean` | `New.sq_le_norm_det_blockDiagPart` | `Matrix.IsHermitian.det_abs` | `Mathlib/Analysis/Matrix/Order.lean` |
| `src/Lib/DiscreteSeries/Haar/CayleyChart.lean` | `New.Haar.det_eq_mul_of_fst_eq_of_snd_eq` | `LinearMap.det_prodMap` | `Mathlib/LinearAlgebra/Determinant.lean` |
| `src/Lib/DiscreteSeries/Haar/TotalMass.lean` | `IsProperMap.monoidHom_id` | `isProperMap_id` | `Mathlib/Topology/Maps/Proper/Basic.lean` |
| `src/Lib/DiscreteSeries/Haar/TotalMass.lean` | `New.measurePreserving_normSq_sphereDensity` | `MeasureTheory.Measure.volumeIoiPow_apply_Iio` | `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` |
| `src/Lib/GLn/Branching/NormBound.lean` | `New.GL.frontPermutation_val` | `Fin.cycleRange_apply` | `Mathlib/GroupTheory/Perm/Fin.lean` |
| `src/Lib/GaloisRep/KillingPolynomials.lean` | `New.powMinor_diagonal_X_mul_eq_zero` | `Matrix.charpoly.optionEquivLeft_symm_univ_isHomogeneous` | `Mathlib/LinearAlgebra/Matrix/Charpoly/Univ.lean` |
| `src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean` | `New.blockDiagonalAlgHom` | `Matrix.blockDiagonal'RingHom` | `Mathlib/Data/Matrix/Block.lean` |
| `src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean` | `New.eq_zero_iff_trace_eq_zero_of_isIdempotentElem` | `LinearMap.IsIdempotentElem.trace_eq_zero_iff` | `Mathlib/LinearAlgebra/Trace.lean` |
| `src/Lib/GaloisRep/Pseudocharacter/SemisimpleRepresentations.lean` | `New.trace_of_idempotent` | `LinearMap.IsIdempotentElem.trace_eq_zero_iff` | `Mathlib/LinearAlgebra/Trace.lean` |
| `src/Lib/General/Algebra/AdicCompletion.lean` | `New.norm_p_lt_one` | `Padic.norm_p_lt_one` | `Mathlib/NumberTheory/Padics/PadicNumbers.lean` |
| `src/Lib/General/Algebra/FittingIdealsAndLengths.lean` | `New.exists_matrix_addVal_det_le_length` | `Submodule.finiteQuotient_iff` | `Mathlib/LinearAlgebra/FreeModule/Finite/Quotient.lean` |
| `src/Lib/General/Algebra/IntegralPowerSeries.lean` | `New.jet_subst_linearSeries` | `MvPowerSeries.constantCoeff_subst_eq_zero` | `Mathlib/RingTheory/MvPowerSeries/Substitution.lean` |
| `src/Lib/General/Algebra/IntegralPowerSeries.lean` | `New.pderiv_subst` | `PowerSeries.derivative_subst` | `Mathlib/RingTheory/PowerSeries/Derivative.lean` |
| `src/Lib/General/Algebra/LongExactSequences.lean` | `New.Variety.H.sigma_bijective` | `CategoryTheory.Functor.mapExt_bijective_of_preservesInjectiveObjects`, `CategoryTheory.hasExt_of_enoughInjectives` | `Mathlib/Algebra/Homology/DerivedCategory/Ext/EnoughInjectives.lean`, `Mathlib/Algebra/Homology/DerivedCategory/Ext/MapBijective.lean` |
| `src/Lib/General/Algebra/MultivariatePolynomials.lean` | `New.Variety.IsAbsIntegrallyClosedLocal.multivariate_hensel` | the `Algebra.Etale` instance | `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean` |
| `src/Lib/General/Algebra/MultivariatePolynomials.lean` | `New.nullstellensatz_exists_le_ker` | `finite_of_algHom_finiteType_of_isJacobsonRing`, `MvPolynomial.eq_vanishingIdeal_singleton_of_isMaximal` | `Mathlib/RingTheory/Jacobson/Ring.lean`, `Mathlib/RingTheory/Nullstellensatz.lean` |
| `src/Lib/General/Algebra/PerfectAlgebras.lean` | `New.Variety.exists_etale_lift` | the `Algebra.Etale` instance | `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean` |
| `src/Lib/General/Algebra/SeriesCongruences.lean` | `New.degree_le_order_prod_pow` | `MvPowerSeries.truncTotal_subst_eq_truncTotal_subst_sum` | `Mathlib/RingTheory/MvPowerSeries/Substitution.lean` |
| `src/Lib/General/Algebra/SharpMinors.lean` | `New.Selmer.exists_span_row_eq_rowLattice` | `Submodule.finiteQuotient_iff` | `Mathlib/LinearAlgebra/FreeModule/Finite/Quotient.lean` |
| `src/Lib/General/Analysis/FourierTransforms.lean` | `New.IsDualFamily.fourier_inversion` | `UnitAddTorus.hasSum_mFourier_series_of_summable` | `Mathlib/Analysis/Fourier/AddCircleMulti.lean` |
| `src/Lib/General/Analysis/HolomorphicIntegrals.lean` | `New.eventually_differentiableAt_integral` | `hasFDerivAt_integral_of_dominated_loc_of_lip` | `Mathlib/Analysis/Calculus/ParametricIntegral.lean` |
| `src/Lib/General/Analysis/MeanValueAndTaylor.lean` | `New.exists_contDiff_eventuallyEq` | `SmoothBumpFunction.contMDiff_smul`, `SmoothPartitionOfUnity.contMDiff_smul` | `Mathlib/Geometry/Manifold/BumpFunction.lean`, `Mathlib/Geometry/Manifold/PartitionOfUnity.lean` |
| `src/Lib/General/Analysis/MeanValueAndTaylor.lean` | `New.taylorAtZero_mul` | `UpperHalfPlane.qExpansion_mul` | `Mathlib/NumberTheory/ModularForms/QExpansion.lean` |
| `src/Lib/General/Analysis/PackingAndSobolev.lean` | `New.encard_le_of_separated` | `Besicovitch.card_le_of_separated` | `Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean` |
| `src/Lib/General/Combinatorics.lean` | `rootCoeffEval_map` | `WittVector.IsPoly.map` | `Mathlib/RingTheory/WittVector/IsPoly.lean` |
| `src/Lib/General/Geometry/DenseComplexPoints.lean` | `New.IsSeparatingFamily.hom_ext` | `AlgebraicGeometry.ext_of_isDominant_of_isSeparated`, `AlgebraicGeometry.ext_of_fromSpecResidueField_eq` | `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` |
| `src/Lib/General/Geometry/DenseComplexPoints.lean` | `New.exists_valuation_le_pow_of_maximalIdeal_le` | `ringKrullDim_eq_one_iff_of_isLocalRing_isDomain` | `Mathlib/RingTheory/KrullDimension/LocalRing.lean` |
| `src/Lib/General/Geometry/DenseComplexPoints.lean` | `New.exists_valuative_arc_of_isDenseFamily` | `AlgebraicGeometry.ValuativeCriterion.Existence.specializingMap` | `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean` |
| `src/Lib/General/Geometry/DenseComplexPoints.lean` | `New.height_map_C_le_one` | `Ideal.map_height_le_one_of_mem_minimalPrimes` | `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean` |
| `src/Lib/General/Geometry/GaloisCovers.lean` | `New.Variety.IsGaloisCovering.etale_of_isPullback` | `Algebra.FormallyEtale.equivPiOfIsSepClosed` | `Mathlib/RingTheory/Etale/Field.lean` |
| `src/Lib/General/Geometry/GaloisCovers.lean` | `New.exists_ringEquiv_extend` | `IsAlgClosed.equivOfTranscendenceBasis`, `IsAlgClosed.ringEquiv_of_equiv_of_charZero` | `Mathlib/FieldTheory/IsAlgClosed/Classification.lean` |
| `src/Lib/General/Geometry/GeometricPoints.lean` | `New.dense_smoothLocus_of_isDenseFamily` | `AlgebraicGeometry.Scheme.Hom.genericPoint_mem_smoothLocus_of_perfectField` | `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` |
| `src/Lib/General/Geometry/GeometricPoints.lean` | `New.stalkMap_injective_of_flat` | `AlgebraicGeometry.Flat.epi_of_flat_of_surjective` | `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean` |
| `src/Lib/General/Geometry/GeometricPoints.lean` | instance `Flat (fromSpecStalk Z s)` | `AlgebraicGeometry.IsAffineOpen.fromSpecStalk_isPreimmersion` | `Mathlib/AlgebraicGeometry/Stalk.lean` |
| `src/Lib/General/Geometry/PointsOfProperSchemes.lean` | `New.Variety.isProperOver_pointsToBase` | `AlgebraicGeometry.IsSeparated.hasAffineProperty` | `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` |
| `src/Lib/General/Geometry/PointsOfProperSchemes.lean` | `le_ker_iff_factors` | `AlgebraicGeometry.eq_bot_of_comp_quotientMk_eq_sigmaSpec` | `Mathlib/AlgebraicGeometry/PointsPi.lean` |
| `src/Lib/General/Groups/IndexOfProduct.lean` | `New.Seesaw.index_pi_univ` | `Subgroup.index_pi` | `Mathlib/GroupTheory/Index.lean` |
| `src/Lib/General/LinearAlgebra/PolarDecomposition.lean` | `New.exists_orthonormal_mul` | `LDL.lowerInv`, `IsWellFounded.wellOrderExtension` | `Mathlib/Analysis/Matrix/LDL.lean`, `Mathlib/Order/Extension/Well.lean` |
| `src/Lib/General/Measure/IntegralOperators.lean` | `New.IsL2Contraction.pi_fin` | `MeasureTheory.Integrable.fin_nat_prod`, `MeasureTheory.integral_fin_nat_prod_eq_prod` | `Mathlib/MeasureTheory/Integral/Pi.lean` |
| `src/Lib/General/Measure/IntegralOperators.lean` | `New.IsL2Contraction.pi` | `MeasureTheory.integral_fintype_prod_eq_prod` | `Mathlib/MeasureTheory/Integral/Pi.lean` |
| `src/Lib/General/Measure/IntegralOperators.lean` | `New.lintegral_pi_prod` | `MeasureTheory.integral_fintype_prod_eq_prod` | `Mathlib/MeasureTheory/Integral/Pi.lean` |
| `src/Lib/General/Measure/IntegralOperators.lean` | `New.measurePreserving_sigma` | `MeasureTheory.measurePreserving_piEquivPiSubtypeProd`, `MeasureTheory.Measure.infinitePi_map_piCurry` | `Mathlib/MeasureTheory/Constructions/Pi.lean`, `Mathlib/Probability/ProductMeasure.lean` |
| `src/Lib/General/Measure/QuadricDisintegration.lean` | `New.Floors.continuous_lintegral_and_lt_top` | `continuousOn_integral_of_compact_support` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` |
| `src/Lib/General/Measure/QuadricDisintegration.lean` | `New.Floors.continuous_lintegral_of_compact_support` | `continuousOn_integral_of_compact_support` | `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` |
| `src/Lib/General/NumberTheory/CMFields.lean` | `New.isCMField_of_forall_exists_conj` | `NumberField.IsCMField.of_forall_isConj` | `Mathlib/NumberTheory/NumberField/CMField.lean` |
| `src/Lib/General/NumberTheory/ImaginaryQuadraticField.lean` | `totient_mul_totient_le_finrank` | `IsPrimitiveRoot.lcm_totient_le_finrank` | `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean` |
| `src/Lib/General/NumberTheory/LatticeCovolumes.lean` | `New.exists_isAddFundamentalDomain_of_integral` | `IsZLattice.basis` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` |
| `src/Lib/General/NumberTheory/SUnitsAndClassNumber.lean` | `New.SUnit.dirichlet_unit_theorem` | `IsDedekindDomain.selmerGroup.valuation_ker_eq` | `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean` |
| `src/Lib/LocalGL/Green/HallAlgebra.lean` | `New.Hall.charpoly_endOnSub_mul_endOnQuot` | `LinearMap.det_eq_det_mul_det` | `Mathlib/LinearAlgebra/Determinant.lean` |
| `src/Lib/PadicComparison/Completion.lean` | `New.Variety.IsSMulDivisible` | `IsSMulRegular` | `Mathlib/Algebra/Regular/SMul.lean` |
| `src/Lib/PadicComparison/Descent/TestCategory.lean` | `New.Variety.isSMulRegular_tensor_of_flat_mod` | `Module.Flat.trans`, `IsSMulRegular.lTensor` | `Mathlib/RingTheory/Regular/IsSMulRegular.lean`, `Mathlib/RingTheory/Flat/Stability.lean` |
| `src/Lib/PadicComparison/HodgeTate/GenericFibre.lean` | `New.Variety.PadicTest.thetaGeneric` | `fontaineThetaInvertP` | `Mathlib/RingTheory/Perfectoid/BDeRham.lean` |
| `src/Lib/PadicHodge/Crystalline/HodgeTateJumps.lean` | `Matrix.det_eq_mul_det_updateCol_of_mulVec_eq_smul_of_apply_eq_one` | `Matrix.mulVec_cramer` | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` |
| `src/Lib/PadicHodge/Kisin/Modules.lean` | `New.Lift.KummerChart.JumpLattice.ainfLattice_eq_span_basis` | `Module.Basis.ofZLatticeBasis` | `Mathlib/Algebra/Module/ZLattice/Basic.lean` |
| `src/Lib/PadicHodge/PeriodRings/Ainf.lean` | `New.Period.smul_frobEnd` | `MulAction.prodEquiv` | `Mathlib/Algebra/Group/Action/Prod.lean` |
| `src/Lib/PadicHodge/PeriodRings/AxTheorem.lean` | `New.Period.norm_zeta_sub_one_pow` | `IsCyclotomicExtension.Rat.associated_zeta_sub_one_pow_prime` | `Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean` |
| `src/Lib/PadicHodge/PeriodRings/AxTheorem.lean` | `New.Variety.wittVector_ringHom_ext_of_teichmuller` | `WittVector.eq_of_apply_teichmuller_eq` | `Mathlib/RingTheory/WittVector/TeichmullerSeries.lean` |
| `src/Lib/PadicHodge/PeriodRings/AxTheorem.lean` | `intQpBar` | `PadicComplexInt` | `Mathlib/NumberTheory/Padics/Complex.lean` |
| `src/Lib/PadicHodge/PeriodRings/AxTheorem.lean` | instance `IsDomain (PreTilt R p)` | `PreTilt.isDomain` | `Mathlib/RingTheory/Perfection.lean` |
| `src/Lib/Shimura/AbelianScheme/Basic.lean` | `New.AddObj` | `CategoryTheory.CommGrpObj` | `Mathlib/CategoryTheory/Monoidal/Cartesian/CommGrp_.lean` |
| `src/Lib/Shimura/AbelianScheme/Basic.lean` | `New.pullbackAddObj` | `CategoryTheory.Functor.isCommMonObj_obj` | `Mathlib/CategoryTheory/Monoidal/CommMon_.lean` |
| `src/Lib/Shimura/AbelianScheme/IsogenyFlatness.lean` | `Ideal.map_maximalIdeal_eq_maximalIdeal_of_mem_minimalPrimes` | `isDedekindDomainDvr.of_formallyUnramified` | `Mathlib/RingTheory/Unramified/Dedekind.lean` |
| `src/Lib/Shimura/ComplexTheta/AppellHumbertData.lean` | `New.coe_fourierChar_eq_exp` | `Real.fourierChar_apply` | `Mathlib/Analysis/Complex/Circle.lean` |
| `src/Lib/Shimura/Eigenspace.lean` | `exists_isEigenQuotient` | `PiTensorProduct.submodule_span_eq_top` | `Mathlib/LinearAlgebra/PiTensorProduct/Generators.lean` |
| `src/Lib/Shimura/HeckeTower/Model.lean` | `New.card_torsionBySet_adelicTorsion` | `NumberField.absNorm_differentIdeal` | `Mathlib/NumberTheory/NumberField/Discriminant/Different.lean` |
| `src/Lib/Shimura/HeckeTower/Model.lean` | `entryConj` | `MonoidHom.restrict` | `Mathlib/Algebra/Group/Submonoid/Operations.lean` |
| `src/Lib/Shimura/ThetaModuli/FamilyFromPoints.lean` | `New.smooth_of_allSpecializeTo_isReduced` | `AlgebraicGeometry.Smooth.of_smooth_fiberToSpecResidueField`, `AlgebraicGeometry.smooth_of_grpObj_of_isAlgClosed` | `Mathlib/AlgebraicGeometry/Group/Smooth.lean`, `Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean` |
| `src/Lib/Shimura/ThetaNormality/NormalGeneration.lean` | `New.ThetaTori.map_homogeneousSubmodule_eq_formSpan` | `Ideal.span_pow_eq_map_homogeneousSubmodule` | `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean` |
| `src/Lib/Shimura/Uniformisation/HolomorphicFamilies.lean` | `New.relIndex_comap_eq_det_mul_conj_det` | `ZLattice.covolume_div_covolume_eq_relIndex` | `Mathlib/Algebra/Module/ZLattice/Covolume.lean` |
| `src/Lib/SiegelWeil/Tower/LineGaussSums.lean` | `New.Exchange.stdColDatum_one_mul_mul` | `Matrix.det_conj_of_mul_eq_one` | `Mathlib/LinearAlgebra/Determinant.lean` |
| `src/Lib/Weil/Construction/FourierInversion.lean` | `New.relIndex_map_nsmul_toAddSubgroup` | `AddSubgroup.relIndex_map_nsmul` | `Mathlib/GroupTheory/IndexNSmul.lean` |
| `src/Lib/Weil/DualPair/Kronecker.lean` | `New.kroneckerGL` | `Matrix.GeneralLinearGroup.kronecker` | `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` |
| `src/Lib/Weil/Unramified/HeckeGL.lean` | `New.eventually_localCongruence_subset` | `Valued.tendsto_zero_pow_of_v_lt_one` | `Mathlib/Topology/Algebra/Valued/WithZeroMulInt.lean` |
| `src/New/Congruences/FirstOrder/OnePrime.lean` | `New.Patching.commutingProd` | `Subgroup.noncommPiCoprod` | `Mathlib/GroupTheory/NoncommPiCoprod.lean` |
| `src/New/Congruences/FirstOrder/OnePrime.lean` | `New.Patching.transfer_eq_prod_cosetComponent` | `MonoidHom.transfer_def`, `Subgroup.leftTransversals.diff` | `Mathlib/GroupTheory/Transfer.lean` |
| `src/New/Congruences/FirstOrder/RibetMethod.lean` | `New.blockFlattenAlgEquiv` | `Matrix.compAlgEquiv` | `Mathlib/Data/Matrix/Composition.lean` |
| `src/New/Congruences/Lifting/CupOrthogonalityBounds.lean` | `New.Lift.length_quotient_mul_length_residueField` | `Ideal.sum_ramification_inertia_eq_finrank_fiber` | `Mathlib/RingTheory/RamificationInertia/Basic.lean` |
| `src/New/Congruences/Selmer/AuxiliaryPrimes.lean` | `pointChar` | `AddChar.zmodChar` | `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean` |
| `src/New/Congruences/Selmer/Mirror.lean` | `New.Selmer.SelmerDatum.exists_linearMap_apply_eq_dualSelmer_conj` | `Module.FinitePresentation.exists_lift_of_isLocalizedModule` | `Mathlib/Algebra/Module/FinitePresentation.lean` |
| `src/New/Derivatives/Field/WeilData.lean` | `New.Parameters.norm_zeta_sub_one_eq_one` | `IsPrimitiveRoot.norm_toInteger_sub_one_eq_one` | `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean` |
| `src/New/Reduction/Zeros/PrimeError.lean` | `New.LSeries_lambdaKResidueClass` | `LSeries_eq_mul_integral_aux` | `Mathlib/NumberTheory/LSeries/SumCoeff.lean` |
| `src/New/Spanning/Bessel/GramSection.lean` | `IsBoundedInCell.isUnit_det_and_norm_inv_le` | `Units.add` | `Mathlib/Analysis/Normed/Ring/Units.lean` |
| `src/New/Spanning/Bessel/GramSection.lean` | `New.RealPlace.norm_fderiv_sectionMatrix_le` | `Complex.norm_fderiv_le_div_of_mapsTo_ball` | `Mathlib/Analysis/Complex/Schwarz.lean` |
| `src/New/Spanning/RemainingTerms/OneRealPlace.lean` | `New.RealPlace.norm_det_subframeBlock` | `Matrix.mulVec_cramer` | `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` |
| `src/New/Spanning/SecondMoment/PositiveType.lean` | `New.expect_addChar_dotProduct` | `AddChar.expect_eq_ite` | `Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean` |
| `src/New/UpperBound/Seesaw/IntegralAsCosetSum.lean` | `New.Seesaw.exists_index_dvd_pow_of_pow_mem` | `IsPGroup.index` | `Mathlib/GroupTheory/PGroup.lean` |

## Copyright and author lines of these Mathlib files

| Mathlib file | copyright | authors |
|---|---|---|
| `Mathlib/Algebra/Algebra/Defs.lean` | Copyright (c) 2018 Kenny Lau. All rights reserved. | Authors: Kenny Lau, Yury Kudryashov |
| `Mathlib/Algebra/Algebra/RestrictScalars.lean` | Copyright (c) 2018 Kenny Lau. All rights reserved. | Authors: Kenny Lau, Yury Kudryashov |
| `Mathlib/Algebra/DirectSum/LinearMap.lean` | Copyright (c) 2023 Oliver Nash. All rights reserved. | Authors: Oliver Nash |
| `Mathlib/Algebra/Group/Action/Prod.lean` | Copyright (c) 2018 Simon Hudon. All rights reserved. | Authors: Simon Hudon, Patrick Massot, Eric Wieser |
| `Mathlib/Algebra/Group/Submonoid/Operations.lean` | Copyright (c) 2018 Johannes Hölzl. All rights reserved. | Authors: Johannes Hölzl, Kenny Lau, Johan Commelin, Mario Carneiro, Kevin Buzzard, Amelia Livingston, Yury Kudryashov |
| `Mathlib/Algebra/Homology/CommSq.lean` | Copyright (c) 2024 Joël Riou. All rights reserved. | Authors: Joël Riou |
| `Mathlib/Algebra/Homology/DerivedCategory/Ext/EnoughInjectives.lean` | Copyright (c) 2025 Joël Riou. All rights reserved. | Authors: Joël Riou |
| `Mathlib/Algebra/Homology/DerivedCategory/Ext/MapBijective.lean` | Copyright (c) 2025 Nailin Guan. All rights reserved. | Authors: Nailin Guan |
| `Mathlib/Algebra/Module/FinitePresentation.lean` | Copyright (c) 2024 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/Algebra/Module/ZLattice/Basic.lean` | Copyright (c) 2023 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/Algebra/Module/ZLattice/Covolume.lean` | Copyright (c) 2024 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/Algebra/Regular/SMul.lean` | Copyright (c) 2021 Damiano Testa. All rights reserved. | Authors: Damiano Testa |
| `Mathlib/AlgebraicGeometry/Group/Smooth.lean` | Copyright (c) 2026 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/AlgebraicGeometry/Morphisms/Flat.lean` | Copyright (c) 2024 Christian Merten. All rights reserved. | Authors: Christian Merten, Andrew Yang |
| `Mathlib/AlgebraicGeometry/Morphisms/Separated.lean` | Copyright (c) 2024 Christian Merten. All rights reserved. | Authors: Christian Merten, Andrew Yang |
| `Mathlib/AlgebraicGeometry/Morphisms/Smooth.lean` | Copyright (c) 2024 Christian Merten. All rights reserved. | Authors: Christian Merten |
| `Mathlib/AlgebraicGeometry/Morphisms/SmoothFiber.lean` | Copyright (c) 2026 Christian Merten. All rights reserved. | Authors: Christian Merten |
| `Mathlib/AlgebraicGeometry/PointsPi.lean` | Copyright (c) 2024 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/AlgebraicGeometry/Stalk.lean` | Copyright (c) 2024 Andrew Yang. All rights reserved. | Authors: Andrew Yang, Fangming Li |
| `Mathlib/AlgebraicGeometry/ValuativeCriterion.lean` | Copyright (c) 2024 Andrew Yang, Qi Ge, Christian Merten. All rights reserved. | Authors: Andrew Yang, Qi Ge, Christian Merten |
| `Mathlib/Analysis/Calculus/LogDeriv.lean` | Copyright (c) 2024 Chris Birkbeck. All rights reserved. | Authors: Chris Birkbeck |
| `Mathlib/Analysis/Calculus/ParametricIntegral.lean` | Copyright (c) 2021 Patrick Massot. All rights reserved. | Authors: Patrick Massot |
| `Mathlib/Analysis/Complex/Circle.lean` | Copyright (c) 2021 Heather Macbeth. All rights reserved. | Authors: Heather Macbeth |
| `Mathlib/Analysis/Complex/Schwarz.lean` | Copyright (c) 2022 Yury Kudryashov. All rights reserved. | Authors: Yury Kudryashov |
| `Mathlib/Analysis/Fourier/AddCircleMulti.lean` | Copyright (c) 2023 David Loeffler. All rights reserved. | Authors: David Loeffler |
| `Mathlib/Analysis/Fourier/FiniteAbelian/Orthogonality.lean` | Copyright (c) 2023 Yaël Dillies, Bhavik Mehta. All rights reserved. | Authors: Yaël Dillies, Bhavik Mehta |
| `Mathlib/Analysis/Matrix/LDL.lean` | Copyright (c) 2022 Alexander Bentkamp. All rights reserved. | Authors: Alexander Bentkamp |
| `Mathlib/Analysis/Matrix/Order.lean` | Copyright (c) 2025 Monica Omar. All rights reserved. | Authors: Monica Omar |
| `Mathlib/Analysis/Normed/Ring/Units.lean` | Copyright (c) 2020 Heather Macbeth. All rights reserved. | Authors: Heather Macbeth |
| `Mathlib/CategoryTheory/Monoidal/Cartesian/CommGrp_.lean` | Copyright (c) 2025 Yaël Dillies. All rights reserved. | Authors: Yaël Dillies |
| `Mathlib/CategoryTheory/Monoidal/CommMon_.lean` | Copyright (c) 2020 Kim Morrison. All rights reserved. | Authors: Kim Morrison |
| `Mathlib/CategoryTheory/Yoneda.lean` | Copyright (c) 2017 Kim Morrison. All rights reserved. | Authors: Kim Morrison |
| `Mathlib/Data/Int/CardIntervalMod.lean` | Copyright (c) 2024 Jeremy Tan. All rights reserved. | Authors: Jeremy Tan |
| `Mathlib/Data/Matrix/Block.lean` | Copyright (c) 2018 Ellen Arlt. All rights reserved. | Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin |
| `Mathlib/Data/Matrix/Composition.lean` | Copyright (c) 2024 Yunzhou Xie. All rights reserved. | Authors: Kevin Buzzard, Yunzhou Xie, Eric Wieser |
| `Mathlib/FieldTheory/IsAlgClosed/Classification.lean` | Copyright (c) 2022 Chris Hughes. All rights reserved. | Authors: Chris Hughes |
| `Mathlib/FieldTheory/KummerPolynomial.lean` | Copyright (c) 2023 Andrew Yang, Patrick Lutz. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/Geometry/Manifold/BumpFunction.lean` | Copyright (c) 2021 Yury Kudryashov. All rights reserved. | Authors: Yury Kudryashov |
| `Mathlib/Geometry/Manifold/PartitionOfUnity.lean` | Copyright (c) 2021 Yury Kudryashov. All rights reserved. | Authors: Yury Kudryashov |
| `Mathlib/GroupTheory/GroupAction/Quotient.lean` | Copyright (c) 2018 Chris Hughes. All rights reserved. | Authors: Chris Hughes, Thomas Browning |
| `Mathlib/GroupTheory/Index.lean` | Copyright (c) 2021 Thomas Browning. All rights reserved. | Authors: Thomas Browning |
| `Mathlib/GroupTheory/IndexNSmul.lean` | Copyright (c) 2026 Michael Stoll. All rights reserved. | Authors: Michael Stoll |
| `Mathlib/GroupTheory/NoncommPiCoprod.lean` | Copyright (c) 2022 Joachim Breitner. All rights reserved. | Authors: Joachim Breitner |
| `Mathlib/GroupTheory/PGroup.lean` | Copyright (c) 2018 Chris Hughes. All rights reserved. | Authors: Chris Hughes, Thomas Browning, Snir Broshi |
| `Mathlib/GroupTheory/Perm/Fin.lean` | Copyright (c) 2021 Eric Wieser. All rights reserved. | Authors: Eric Wieser, Yi Yuan |
| `Mathlib/GroupTheory/Transfer.lean` | Copyright (c) 2022 Thomas Browning. All rights reserved. | Authors: Thomas Browning |
| `Mathlib/LinearAlgebra/Determinant.lean` | Copyright (c) 2019 Johannes Hölzl. All rights reserved. | Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen |
| `Mathlib/LinearAlgebra/ExteriorAlgebra/Basic.lean` | Copyright (c) 2020 Adam Topaz. All rights reserved. | Authors: Zhangir Azerbayev, Adam Topaz, Eric Wieser |
| `Mathlib/LinearAlgebra/FreeModule/Finite/Quotient.lean` | Copyright (c) 2025 Xavier Roblot. All rights reserved. | Authors: Anne Baanen, Xavier Roblot |
| `Mathlib/LinearAlgebra/Matrix/Adjugate.lean` | Copyright (c) 2019 Anne Baanen. All rights reserved. | Authors: Anne Baanen |
| `Mathlib/LinearAlgebra/Matrix/Charpoly/Basic.lean` | Copyright (c) 2020 Kim Morrison. All rights reserved. | Authors: Kim Morrison |
| `Mathlib/LinearAlgebra/Matrix/Charpoly/Univ.lean` | Copyright (c) 2024 Johan Commelin. All rights reserved. | Authors: Johan Commelin |
| `Mathlib/LinearAlgebra/Matrix/GeneralLinearGroup/Defs.lean` | Copyright (c) 2021 Chris Birkbeck. All rights reserved. | Authors: Chris Birkbeck |
| `Mathlib/LinearAlgebra/PiTensorProduct/Generators.lean` | Copyright (c) 2026 Joël Riou. All rights reserved. | Authors: Joël Riou |
| `Mathlib/LinearAlgebra/Trace.lean` | Copyright (c) 2019 Johannes Hölzl. All rights reserved. | Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen, Antoine Labelle |
| `Mathlib/MeasureTheory/Constructions/HaarToSphere.lean` | Copyright (c) 2023 Yury Kudryashov. All rights reserved. | Authors: Yury Kudryashov |
| `Mathlib/MeasureTheory/Constructions/Pi.lean` | Copyright (c) 2020 Floris van Doorn. All rights reserved. | Authors: Floris van Doorn |
| `Mathlib/MeasureTheory/Covering/BesicovitchVectorSpace.lean` | Copyright (c) 2021 Sébastien Gouëzel. All rights reserved. | Authors: Sébastien Gouëzel |
| `Mathlib/MeasureTheory/Group/Prod.lean` | Copyright (c) 2021 Floris van Doorn. All rights reserved. | Authors: Floris van Doorn |
| `Mathlib/MeasureTheory/Integral/Bochner/Set.lean` | Copyright (c) 2020 Zhouhang Zhou. All rights reserved. | Authors: Zhouhang Zhou, Yury Kudryashov |
| `Mathlib/MeasureTheory/Integral/Pi.lean` | Copyright (c) 2023 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/MeasureTheory/Measure/Typeclasses/Finite.lean` | Copyright (c) 2017 Johannes Hölzl. All rights reserved. | Authors: Johannes Hölzl, Mario Carneiro |
| `Mathlib/NumberTheory/Cyclotomic/CyclotomicCharacter.lean` | Copyright (c) 2023 Hanneke Wiersema. All rights reserved. | Authors: Kevin Buzzard, Hanneke Wiersema, Andrew Yang |
| `Mathlib/NumberTheory/Cyclotomic/PrimitiveRoots.lean` | Copyright (c) 2022 Riccardo Brasca. All rights reserved. | Authors: Alex J. Best, Riccardo Brasca, Eric Rodriguez |
| `Mathlib/NumberTheory/LSeries/DirichletContinuation.lean` | Copyright (c) 2024 David Loeffler. All rights reserved. | Authors: David Loeffler, Michael Stoll |
| `Mathlib/NumberTheory/LSeries/PrimesInAP.lean` | Copyright (c) 2024 Michael Stoll. All rights reserved. | Authors: Michael Stoll |
| `Mathlib/NumberTheory/LSeries/SumCoeff.lean` | Copyright (c) 2025 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/NumberTheory/LegendreSymbol/AddCharacter.lean` | Copyright (c) 2022 Michael Stoll. All rights reserved. | Authors: Michael Stoll |
| `Mathlib/NumberTheory/MahlerMeasure.lean` | Copyright (c) 2025 Fabrizio Barroero. All rights reserved. | Authors: Fabrizio Barroero |
| `Mathlib/NumberTheory/ModularForms/EisensteinSeries/IsBoundedAtImInfty.lean` | Copyright (c) 2024 Chris Birkbeck. All rights reserved. | Authors: Chris Birkbeck |
| `Mathlib/NumberTheory/ModularForms/LevelOne/DimensionFormula.lean` | Copyright (c) 2026 Chris Birkbeck. All rights reserved. | Authors: Chris Birkbeck |
| `Mathlib/NumberTheory/ModularForms/QExpansion.lean` | Copyright (c) 2024 David Loeffler. All rights reserved. | Authors: David Loeffler |
| `Mathlib/NumberTheory/NumberField/CMField.lean` | Copyright (c) 2025 X. Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/NumberTheory/NumberField/Cyclotomic/Basic.lean` | Copyright (c) 2022 Riccardo Brasca. All rights reserved. | Authors: Riccardo Brasca |
| `Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean` | Copyright (c) 2025 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/NumberTheory/NumberField/Discriminant/Different.lean` | Copyright (c) 2025 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/NumberTheory/NumberField/InfinitePlace/Basic.lean` | Copyright (c) 2022 Xavier Roblot. All rights reserved. | Authors: Xavier Roblot |
| `Mathlib/NumberTheory/Padics/Complex.lean` | Copyright (c) 2025 María Inés de Frutos-Fernández. All rights reserved. | Authors: María Inés de Frutos-Fernández |
| `Mathlib/NumberTheory/Padics/PadicNumbers.lean` | Copyright (c) 2018 Robert Y. Lewis. All rights reserved. | Authors: Robert Y. Lewis |
| `Mathlib/NumberTheory/PrimesCongruentOne.lean` | Copyright (c) 2020 Riccardo Brasca. All rights reserved. | Authors: Riccardo Brasca |
| `Mathlib/NumberTheory/RamificationInertia/Basic.lean` | Copyright (c) 2022 Anne Baanen. All rights reserved. | Authors: Anne Baanen |
| `Mathlib/NumberTheory/RamificationInertia/Galois.lean` | Copyright (c) 2024 Yongle Hu. All rights reserved. | Authors: Yongle Hu, Jiedong Jiang |
| `Mathlib/Order/Extension/Well.lean` | Copyright (c) 2022 Yaël Dillies, Junyan Xu. All rights reserved. | Authors: Yaël Dillies, Junyan Xu |
| `Mathlib/Order/Northcott.lean` | Copyright (c) 2026 Thomas Browning. All rights reserved. | Authors: Thomas Browning |
| `Mathlib/Probability/ProductMeasure.lean` | Copyright (c) 2025 Etienne Marion. All rights reserved. | Authors: Etienne Marion |
| `Mathlib/RepresentationTheory/Coinduced.lean` | Copyright (c) 2025 Amelia Livingston. All rights reserved. | Authors: Amelia Livingston |
| `Mathlib/RepresentationTheory/Invariants.lean` | Copyright (c) 2022 Antoine Labelle. All rights reserved. | Authors: Antoine Labelle |
| `Mathlib/RingTheory/DedekindDomain/Different.lean` | Copyright (c) 2023 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/RingTheory/DedekindDomain/SelmerGroup.lean` | Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved. | Authors: David Kurniadi Angdinata |
| `Mathlib/RingTheory/Etale/Field.lean` | Copyright (c) 2024 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/RingTheory/Flat/Stability.lean` | Copyright (c) 2024 Christian Merten. All rights reserved. | Authors: Christian Merten |
| `Mathlib/RingTheory/Ideal/KrullsHeightTheorem.lean` | Copyright (c) 2025 Andrew Yang. All rights reserved. | Authors: Wanyi He, Jiedong Jiang, Christian Merten, Jingting Wang, Andrew Yang, Shouxin Zhang |
| `Mathlib/RingTheory/Jacobson/Ring.lean` | Copyright (c) 2020 Devon Tuma. All rights reserved. | Authors: Devon Tuma |
| `Mathlib/RingTheory/KrullDimension/LocalRing.lean` | Copyright (c) 2025 Jingting Wang. All rights reserved. | Authors: Jingting Wang |
| `Mathlib/RingTheory/LinearDisjoint.lean` | Copyright (c) 2024 Jz Pan. All rights reserved. | Authors: Jz Pan |
| `Mathlib/RingTheory/MvPolynomial/Homogeneous.lean` | Copyright (c) 2020 Johan Commelin. All rights reserved. | Authors: Johan Commelin, Eric Wieser |
| `Mathlib/RingTheory/MvPowerSeries/Equiv.lean` | Copyright (c) 2026 Bingyu Xia. All rights reserved. | Authors: Bingyu Xia, Wenrong Zou |
| `Mathlib/RingTheory/MvPowerSeries/Substitution.lean` | Copyright (c) 2024 Antoine Chambert-Loir, María Inés de Frutos Fernández. All rights reserved. | Authors: Antoine Chambert-Loir, María Inés de Frutos Fernández |
| `Mathlib/RingTheory/Nullstellensatz.lean` | Copyright (c) 2021 Devon Tuma. All rights reserved. | Authors: Devon Tuma |
| `Mathlib/RingTheory/Perfection.lean` | Copyright (c) 2020 Kenny Lau. All rights reserved. | Authors: Kenny Lau |
| `Mathlib/RingTheory/Perfectoid/BDeRham.lean` | Copyright (c) 2025 Jiedong Jiang. All rights reserved. | Authors: Jiedong Jiang |
| `Mathlib/RingTheory/Polynomial/GaussLemma.lean` | Copyright (c) 2020 Aaron Anderson. All rights reserved. | Authors: Aaron Anderson |
| `Mathlib/RingTheory/Polynomial/UniversalFactorizationRing.lean` | Copyright (c) 2025 Andrew Yang. All rights reserved. | Authors: Andrew Yang |
| `Mathlib/RingTheory/PowerSeries/Derivative.lean` | Copyright (c) 2023 Richard M. Hill. All rights reserved. | Authors: Richard M. Hill, Ralf Stephan |
| `Mathlib/RingTheory/RamificationInertia/Basic.lean` | Copyright (c) 2026 Thomas Browning. All rights reserved. | Authors: Thomas Browning |
| `Mathlib/RingTheory/Regular/IsSMulRegular.lean` | Copyright (c) 2024 Brendan Murphy. All rights reserved. | Authors: Brendan Murphy |
| `Mathlib/RingTheory/Unramified/Dedekind.lean` | Copyright (c) 2026 Thomas Browning. All rights reserved. | Authors: Thomas Browning |
| `Mathlib/RingTheory/Valuation/LocalSubring.lean` | Copyright (c) 2024 Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu. All rights reserved. | Authors: Andrew Yang, Yaël Dillies, Javier López-Contreras, Daniel Funck, Junyan Xu |
| `Mathlib/RingTheory/WittVector/IsPoly.lean` | Copyright (c) 2020 Johan Commelin. All rights reserved. | Authors: Johan Commelin, Robert Y. Lewis |
| `Mathlib/RingTheory/WittVector/TeichmullerSeries.lean` | Copyright (c) 2025 Jiedong Jiang. All rights reserved. | Authors: Jiedong Jiang |
| `Mathlib/Topology/Algebra/ClopenNhdofOne.lean` | Copyright (c) 2024 Nailin Guan. All rights reserved. | Authors: Nailin Guan, Yi Song, Xuchun Li, Bryan Wang |
| `Mathlib/Topology/Algebra/Module/Basic.lean` | Copyright (c) 2019 Sébastien Gouëzel. All rights reserved. | Authors: Jan-David Salchow, Sébastien Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis, Heather Macbeth |
| `Mathlib/Topology/Algebra/Valued/WithZeroMulInt.lean` | Copyright (c) 2025 Salvatore Mercuri. All rights reserved. | Authors: Salvatore Mercuri |
| `Mathlib/Topology/Compactness/SigmaCompact.lean` | Copyright (c) 2017 Johannes Hölzl. All rights reserved. | Authors: Johannes Hölzl, Mario Carneiro, Yury Kudryashov |
| `Mathlib/Topology/DenseEmbedding.lean` | Copyright (c) 2019 Reid Barton. All rights reserved. | Authors: Johannes Hölzl, Mario Carneiro, Patrick Massot |
| `Mathlib/Topology/Maps/Proper/Basic.lean` | Copyright (c) 2023 Anatole Dedecker. All rights reserved. | Authors: Anatole Dedecker, Etienne Marion |
