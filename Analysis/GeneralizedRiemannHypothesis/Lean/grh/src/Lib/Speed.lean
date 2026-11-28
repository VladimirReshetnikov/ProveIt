import Mathlib

/-!
# Speed settings

The three settings of this file make instance search and `simp` faster in all files of the
development. They add no axiom, and no proof relies on them: with this file emptied, the other files
still compile, more slowly.
-/

-- Instance search tries these instances late (the default priority is 1000). Tried early,
-- they start long searches that fail.
attribute [instance 20] MonTypeEquivalenceMon.monMonoid
  CommMonTypeEquivalenceCommMon.commMonCommMonoid GrpTypeEquivalenceGrp.grpGroup
  IsPurelyInseparable.isIntegral NonUnitalNonAssocSemiring.toAddCommMonoid
  IsDedekindDomain.toIsDomain SetLike.GradeZero.instCommSemiring SetLike.GradeZero.instMonoid
  SetLike.GradeZero.instSemiring SetLike.GradeZero.instRing SetLike.GradeZero.instCommRing
  SetLike.GradeZero.instCommMonoid MulSemiringAction.toDistribMulAction AddQuantale.instAddLeftMono
  AddQuantale.instAddRightMono LieAdmissibleAlgebra.toModule RightPreLieAlgebra.toModule
  LeftPreLieAlgebra.toModule LieAlgebra.toModule LieRing.toAddCommGroup
  Action.FintypeCat.instMulActionObjFiniteOf NonarchimedeanRing.toIsTopologicalRing
  NonarchimedeanAddGroup.toIsTopologicalAddGroup LieRinehartAlgebra.toIsScalarTower
  GroupConeClass.toSubmonoidClass IsAffineAddMonoid.toHasUniqueDiv IsAffineAddMonoid.toIsAddFG
  instNontrivialOfCharZero MeasureTheory.instSFiniteOfCountable
  CategoryTheory.Limits.instHasProductsOfShapeOfHasCountableProductsOfCountable
  CategoryTheory.Limits.instHasCoproductsOfShapeOfHasCountableCoproductsOfCountable
  Torsor.toMulAction GradedMonoid.GradeZero.smul Prod.distribMulAction Prod.instStarModule
  PerfectField.ofFinite littleWedderburn BooleanRing.toRing BooleanRing.toCommRing
  FunLike.toDecidableEq
  Module.free_of_finite_type_torsion_free' IsOrderedCancelAddMonoid.toIsCancelAdd
  instIsLeftCancelAddOfAddLeftReflectLE instSMulZeroClass NonUnitalAlgSemiHomClass.toMulHomClass
  NonUnitalAlgSemiHomClass.toDistribMulActionSemiHomClass CoalgHomClass.toSemilinearMapClass
  RingHomClass.toLinearMapClassNNRat RingHomClass.toLinearMapClassRat
  SemilinearMapClass.toAddHomClass CentroidHomClass.toAddMonoidHomClass BialgHomClass.toAlgHomClass
  MonoidWithZeroHomClass.toZeroHomClass Function.locallyCompactSpace IsAlgClosure.isAlgebraic
  IsPurelyInseparable.normal Quantale.instMulRightMono Quantale.instMulLeftMono
  NonUnitalNonAssocRing.toAddCommGroup CategoryTheory.CountableCategory.countableObj
  CStarAlgebra.instPosPart AddCommMonoidWithOne.toAddCommMonoid BialgHomClass.toMonoidHomClass
  ProperSMul.toContinuousSMul LieAdmissibleRing.toNonUnitalNonAssocRing
  IsValuativeTopology.instIsTopologicalAddGroup SemilinearIsometryClass.toSemilinearMapClass
  AlexandrovDiscrete.toLocallyCompactSpace Valuation.HasExtension.instIsScalarTower_valuationSubring
  OreLocalization.instDistribMulActionOfIsScalarTower Pi.starRing'
  CompletePartialOrder.toPartialOrder Valued.toUniformSpace TotallySeparatedSpace.t2Space
  Lean.Grind.OrderedRing.instIsCharPOfNatNatOfLawfulOrderLT Prod.continuousSMul Prod.isCentralScalar
  Prod.distribSMul Prod.smulZeroClass Prod.continuousConstSMul
  IsSemitopologicalSemiring.toContinuousAdd IsSemitopologicalSemiring.toSeparatelyContinuousMul
  CategoryTheory.Limits.hasColimitsOfShape_discrete Algebra.IsAlgebraic.isIntegral

-- These lemmas leave the default `simp` set of every importing file. They match very many terms
-- and then fail on a side condition. Tagging a lemma in both directions erases both, and, unlike
-- `attribute [-simp]`, the effect passes to importers. The reversed tags last one command only,
-- so the warning about their head symbols does not apply.
set_option warning.simp.varHead false in
attribute [simp ←, simp] Matrix.conjTranspose_eq_transpose_of_trivial MonoidHom.CompTriple.comp_eq
  LinearMap.identityMapOfZeroModuleIsZero LowerAdjoint.closure_le_closed_iff_le smul_left_cancel_iff
  PartialOrder.mkOfAddGroupCone_le_iff mul_cancel_left_mem_nonZeroDivisors IsAddKleinFour.card_four'
  MeasureTheory.lintegral_of_isEmpty PartialOrder.mkOfGroupCone_le_iff Nat.card_eq_zero_of_infinite
  IsRegular.smul_eq_zero_iff_right
  Unitary.star_mul_self_of_mem Representation.isTrivial_def inv_mul_cancel_of_invertible bot_eq_one'
  EmbeddingLike.map_eq_one_iff Submodule.smul_coe_torsionBy Valuation.IsUniformizer.val star_trivial
  SetLike.GradeZero.coe_ofNat Associates.coe_unit_eq_one inv_mul_cancel_comm_assoc nsmul_eq_zero_iff
  SetLike.GradeZero.coe_mul RingHomCompTriple.comp_eq Finset.Ioc_eq_empty_of_le Finset.univ_eq_empty
  IsRegular.smul_right_inj IsAddKleinFour.card_four RootPairing.indexNeg_neg BooleanRing.mul_add_mul
  Submodule.smul_mem_iff' IsKleinFour.card_four' Nat.sub_eq_zero_of_le IsUnit.inv_mul_cancel
  IsUnit.mul_inv_cancel GroupWithZero.dvd_iff Ring.inverse_non_unit ciSup_of_not_bddAbove tsum_empty
  inv_mul_cancel_comm mul_inv_cancel_comm Set.iInter_of_empty CharP.cast_eq_zero IsEmpty.exists_iff
  IsMin.finsetIio_eq Set.Icc_eq_empty RCLike.star_def map_one_eq_zero inf_of_le_right inf_of_le_left
  FunLike.coe_mul Nat.card_unique map_inv_eq_map map_neg_eq_map nhds_discrete smul_left_inj norm_map
  RKHS.coe_smul tsum_comp_neg Nat.sub_self conj_trivial bot_eq_zero'

/-- A synonym of `IsEmpty` about which `simp` knows nothing. -/
def New.IsVoid : Sort* → Prop := IsEmpty

/-- Many `simp` lemmas have a hypothesis `[IsEmpty α]`. When instance search does not find it,
`simp` tries to prove it. This lemma ends the attempt at once. -/
@[simp 1001]
lemma New.isEmpty_iff_isVoid (α : Sort*) : IsEmpty α ↔ IsVoid α := .rfl
