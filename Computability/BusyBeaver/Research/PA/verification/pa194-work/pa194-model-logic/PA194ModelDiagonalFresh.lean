import PA194ModelExEqualityDiagonal
import PA194ModelOneLevelCharacterization
import PA194ModelFreshBoolean
import PA194ModelRankedEnvironment
import PA194ModelUniversalSpecialization
import PA194ModelBinderAllocationShift
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance diagonalFreshZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance diagonalFreshOne : One M := ⟨F oneCode Fin.elim0⟩
local instance diagonalFreshAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance diagonalFreshMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance diagonalFreshLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance diagonalFreshIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]



theorem targetReflexiveDiagonalAll (e : M) :
    TargetProvable (F fixedFormulaTranslation ![^∀ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]),
      simBound e,simFree e,simBase e,simReserve e]) := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  rw [fixedFormulaTranslation_all _ _ _ _ _ hp,fixedTranslation_equalityBoundDiagonal]
  exact tp_gen _ (neighborhood_refl _ _)

theorem targetReflexiveDiagonalEx (e : M) :
    TargetProvable (F fixedFormulaTranslation ![^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]),
      simBound e,simFree e,simBase e,simReserve e]) := by
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]) := by
    simpa only [IsUFormula.rel] using And.intro hr hv
  rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,fixedTranslation_equalityBoundDiagonal]
  exact targetExists_of_bodyTheorem _ _ (neighborhood_refl _ _)

theorem simRuleAllFresh_allEqualityDiagonal (e : M) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))))) := by
  change TargetProvable (impValue (negatedTranslation e _) (allValue (simBase e) (negatedTranslation e _)))
  rw [negatedTranslation_any]
  let A := F fixedFormulaTranslation ![^∀ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]),
    simBound e,simFree e,simBase e,simReserve e]
  let h : Ctx [negValue A] (negValue A) := .assumption (by simp)
  exact (Ctx.mp (.closed (targetReflexiveDiagonalAll e)) h).explosion _ |>.deduction.empty

theorem simRuleAllFresh_exEqualityDiagonal (e : M) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))))) := by
  change TargetProvable (impValue (negatedTranslation e _) (allValue (simBase e) (negatedTranslation e _)))
  rw [negatedTranslation_any]
  let A := F fixedFormulaTranslation ![^∃ (^rel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]),
    simBound e,simFree e,simBase e,simReserve e]
  let h : Ctx [negValue A] (negValue A) := .assumption (by simp)
  exact (Ctx.mp (.closed (targetReflexiveDiagonalEx e)) h).explosion _ |>.deduction.empty

theorem targetNegatedDiagonalAll (e : M) :
    TargetProvable (negatedTranslation e (^∀ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) := by
  rw [negatedTranslation_any]
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]) := by
    simpa only [IsUFormula.nrel] using And.intro hr hv
  rw [fixedFormulaTranslation_all _ _ _ _ _ hp,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,fixedTranslation_equalityBoundDiagonal]
  exact targetExists_of_bodyTheorem _ _ (neighborhood_refl _ _)

theorem targetNegatedDiagonalEx (e : M) :
    TargetProvable (negatedTranslation e (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))) := by
  rw [negatedTranslation_any]
  have hr : SourceL.IsRel (2 : M) (0 : M) := relExt_relation_zero
  have hv : IsUTermVec SourceL 2 (?[ ^#(0 : M),^#(0 : M)] : M) := by simp
  have hp : IsUFormula SourceL (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]) := by
    simpa only [IsUFormula.nrel] using And.intro hr hv
  rw [fixedFormulaTranslation_ex _ _ _ _ _ hp,
    fixedFormulaTranslation_atom_polarity _ _ _ _ _ _ hr hv,fixedTranslation_equalityBoundDiagonal]
  let n := neighborhoodValue (simBase e) (simBase e) (simReserve e)
  have hnn : TargetProvable (negValue (negValue n)) :=
    tp_mp (neighborhood_refl _ _) (doubleNegationIntroduction _)
  have hall : TargetProvable (allValue (simBase e) (negValue (negValue n))) := tp_gen _ hnn
  exact tp_mp hall (doubleNegationIntroduction _)

theorem targetVacuity_of_theorem (x A : M) (h : TargetProvable A) :
    TargetProvable (impValue A (allValue x A)) := by
  let hh : Ctx [A] (allValue x A) := .closed (tp_gen x h)
  exact hh.deduction.empty

theorem simRuleAllFresh_allNegativeEqualityDiagonal (e : M) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∀ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∀ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))))) := by
  change TargetProvable (impValue (negatedTranslation e _) (allValue (simBase e) (negatedTranslation e _)))
  exact targetVacuity_of_theorem (simBase e) _ (targetNegatedDiagonalAll e)

theorem simRuleAllFresh_exNegativeEqualityDiagonal (e : M) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalTranslation.tr e (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)])))
      (numericalQuant.all (simBase e)
        (numericalTranslation.tr e (^∃ (^nrel (2 : M) (0 : M) ?[^#(0 : M),^#(0 : M)]))))) := by
  change TargetProvable (impValue (negatedTranslation e _) (allValue (simBase e) (negatedTranslation e _)))
  exact targetVacuity_of_theorem (simBase e) _ (targetNegatedDiagonalEx e)

#print axioms targetNegatedDiagonalAll
#print axioms targetNegatedDiagonalEx
#print axioms simRuleAllFresh_allNegativeEqualityDiagonal
#print axioms simRuleAllFresh_exNegativeEqualityDiagonal
#print axioms targetReflexiveDiagonalAll
#print axioms targetReflexiveDiagonalEx
#print axioms simRuleAllFresh_allEqualityDiagonal
#print axioms simRuleAllFresh_exEqualityDiagonal
end models
end PA194ModelLogic
