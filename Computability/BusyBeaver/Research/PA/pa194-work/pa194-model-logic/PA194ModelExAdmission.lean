import PA194ModelExNegativeMembership
import PA194ModelSeedEnvironment
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
local instance exAdmissionZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance exAdmissionOne : One M := ⟨F oneCode Fin.elim0⟩
local instance exAdmissionAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance exAdmissionMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance exAdmissionLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance exAdmissionIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]




/-- The positive membership instance at the actual seeded compiler admission. -/
theorem simRuleExs_positiveMembershipSeed (bound reserve e s v t d : M)
    (ha : SeedAdmission bound reserve e (exsIntro s (^rel (2 : M) (1 : M) v) t d))
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^rel (2 : M) (1 : M) v)) ∈ s)
    (ht : IsTerm SourceL t) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^rel (2 : M) (1 : M) v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^rel (2 : M) (1 : M) v))) 1)) :=
  simRuleExs_positiveMembershipCode e s v t _ hs hm ht (depthAdmission_ranked e _ ha.1)

/-- The negative membership instance at the actual seeded compiler admission. -/
theorem simRuleExs_negativeMembershipSeed (bound reserve e s v t d : M)
    (ha : SeedAdmission bound reserve e (exsIntro s (^nrel (2 : M) (1 : M) v) t d))
    (hs : IsFormulaSet SourceL s) (hm : (^∃ (^nrel (2 : M) (1 : M) v)) ∈ s)
    (ht : IsTerm SourceL t) :
    numericalQuant.Pr (numericalQuant.imp
      (numericalQuant.imp (numericalTranslation.tr e (substs1 SourceL t (^nrel (2 : M) (1 : M) v))) 1)
      (numericalQuant.imp (numericalTranslation.tr e (^∃ (^nrel (2 : M) (1 : M) v))) 1)) :=
  simRuleExs_negativeMembershipCode e s v t _ hs hm ht (depthAdmission_ranked e _ ha.1)

#print axioms simRuleExs_positiveMembershipSeed
#print axioms simRuleExs_negativeMembershipSeed
end models
end PA194ModelLogic
