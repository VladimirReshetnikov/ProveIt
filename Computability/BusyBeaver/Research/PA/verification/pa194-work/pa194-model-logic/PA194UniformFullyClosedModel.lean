import PA194UniformFullyClosed
import PA194UniformCloseModel
import PA194ModelClosedSepUniform
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194BindSource
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open PA194ModelLogic
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance pureFullyClosedModelZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance pureFullyClosedModelOne : One M := ⟨F oneCode Fin.elim0⟩
local instance pureFullyClosedModelAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance pureFullyClosedModelMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance pureFullyClosedModelLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance pureFullyClosedModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem pureFullyClosedSeparation_model (p : M) :
    pureFullyClosedSeparation p = fullyClosedSeparation p := by
  simp [pureFullyClosedSeparation,fullyClosedSeparation,sepRootPure_model,
    pureModelClose_model,pureFormulaFreeBound_model]
#print axioms pureFullyClosedSeparation_model
end models
end PA194BindSource
