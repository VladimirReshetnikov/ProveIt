import PA194ModelShiftGeneralReverse
import PA194ModelShiftSameGeneral
import PA194ModelSeedEnvironment
import PA194ModelSafeQF
import PA194ModelExMembership
import PA194ModelSeedEnvironment
import PA194ModelDescendantComplexity
import PA194ModelRankedEnvironment
import PA194ModelDualInduction
import PA194ModelAtomicFreshness
import PA194RelExtTypedTranslation

/-! Internal structural induction for arbitrary-label vacuity. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
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
local instance shiftActualGeneralZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance shiftActualGeneralOne : One M := ⟨F oneCode Fin.elim0⟩
local instance shiftActualGeneralAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance shiftActualGeneralMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance shiftActualGeneralLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance shiftActualGeneralIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem simRuleShift_generalSeed_derivation (T : Theory SourceL) [T.Δ₁]
    (reserve e d q : M)
    (ha : SeedAdmission 0 reserve e (shiftRule (setShift SourceL (fstIdx d)) d))
    (hd : Bootstrapping.Derivation T d) (hq : q ∈ fstIdx d) :
    numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e (shift SourceL q))
      (numericalTranslation.tr (simPopFree e) q)) :=
  simRuleShift_generalSeed_set reserve e d q ha hd.isFormulaSet hq
#print axioms simRuleShift_generalSeed_derivation
end models
end PA194ModelLogic
