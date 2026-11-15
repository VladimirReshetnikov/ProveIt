import PA194ModelExEqualityWitness
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
local instance exAtomWitnessZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance exAtomWitnessOne : One M := ⟨F oneCode Fin.elim0⟩
local instance exAtomWitnessAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance exAtomWitnessMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance exAtomWitnessLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance exAtomWitnessIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]




/-- The complete positive-atom existential field under ranked admission. -/
theorem simRuleExs_positiveAtomCode_fresh (e s r v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) r v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^rel (2 : M) r v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) r v))) 1)) := by
  have hf := (hs _ hm).isUFormula
  have hr := (IsUFormula.rel.mp (IsUFormula.ex.mp hf)).1
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with rfl | rfl
  · exact simRuleExs_equalityCode_fresh e s v t d hs hm ht ha
  · exact simRuleExs_positiveMembershipCode e s v t d hs hm ht ha

/-- The analogous negative-atom field under ranked admission. -/
theorem simRuleExs_negativeAtomCode_fresh (e s r v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) r v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^nrel (2 : M) r v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) r v))) 1)) := by
  have hf := (hs _ hm).isUFormula
  have hr := (IsUFormula.nrel.mp (IsUFormula.ex.mp hf)).1
  have hr' : r = 0 ∨ r = 1 := by
    change ((“k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)” : ArithmeticSemisentence 2).Evalb ![(2 : M),r]) at hr
    simpa using hr
  rcases hr' with rfl | rfl
  · exact simRuleExs_negativeEqualityCode_fresh e s v t d hs hm ht ha
  · exact simRuleExs_negativeMembershipCode e s v t d hs hm ht ha

theorem simRuleExs_positiveRelation_fresh (e s k r v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel k r v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^rel k r v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel k r v))) 1)) := by
  have hf := (hs _ hm).isUFormula
  have hr := (IsUFormula.rel.mp (IsUFormula.ex.mp hf)).1
  have hk := PA194AtomShiftCodeModel.sourceRelation_arity hr
  subst k
  exact simRuleExs_positiveAtomCode_fresh e s r v t d hs hm ht ha

theorem simRuleExs_negativeRelation_fresh (e s k r v t d : M)
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel k r v)) ∈ s)
    (ht : IsTerm SourceL t) (ha : RankedAdmission e d) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^nrel k r v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel k r v))) 1)) := by
  have hf := (hs _ hm).isUFormula
  have hr := (IsUFormula.nrel.mp (IsUFormula.ex.mp hf)).1
  have hk := PA194AtomShiftCodeModel.sourceRelation_arity hr
  subst k
  exact simRuleExs_negativeAtomCode_fresh e s r v t d hs hm ht ha

#print axioms simRuleExs_positiveRelation_fresh
#print axioms simRuleExs_negativeRelation_fresh
#print axioms simRuleExs_positiveAtomCode_fresh
#print axioms simRuleExs_negativeAtomCode_fresh
end models
end PA194ModelLogic
