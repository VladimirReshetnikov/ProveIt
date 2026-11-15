import PA194ModelExEqualityDiagonal
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
local instance exAtomZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance exAtomOne : One M := ⟨F oneCode Fin.elim0⟩
local instance exAtomAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance exAtomMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance exAtomLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance exAtomIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]




/-- The complete positive-atom existential field, with primitive equality
vacuity required only when the atom is equality. -/
theorem simRuleExs_positiveAtomCode (e s r v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) r v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d)
    (heq : r = 0 → TargetProvable (impValue (eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e))
      (allValue (simReserve e) (eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^rel (2 : M) r v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) r v))) 1)) := by
  have hf := (hs _ hm).isUFormula
  have hr := (IsUFormula.rel.mp (IsUFormula.ex.mp hf)).1
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with rfl | rfl
  · exact simRuleExs_equalityCode_of_eqVacuity e s v t d hs hm ht ha (heq rfl)
  · exact simRuleExs_positiveMembershipCode e s v t d hs hm ht ha

/-- The analogous negative-atom field with the same isolated premise. -/
theorem simRuleExs_negativeAtomCode (e s r v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) r v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d)
    (heq : r = 0 → TargetProvable (impValue (eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e))
      (allValue (simReserve e) (eqValue (F termLabelCode ![t,simBound e,simFree e]) (simBase e))))) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^nrel (2 : M) r v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) r v))) 1)) := by
  have hf := (hs _ hm).isUFormula
  have hr := (IsUFormula.nrel.mp (IsUFormula.ex.mp hf)).1
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with rfl | rfl
  · exact simRuleExs_negativeEqualityCode_of_eqVacuity e s v t d hs hm ht ha (heq rfl)
  · exact simRuleExs_negativeMembershipCode e s v t d hs hm ht ha

#print axioms simRuleExs_positiveAtomCode
#print axioms simRuleExs_negativeAtomCode
end models
end PA194ModelLogic
