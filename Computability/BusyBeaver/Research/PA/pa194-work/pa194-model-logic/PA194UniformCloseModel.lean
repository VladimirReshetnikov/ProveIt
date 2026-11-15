import PA194UniformClose
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
local instance pureModelCloseModelZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance pureModelCloseModelOne : One M := ⟨F oneCode Fin.elim0⟩
local instance pureModelCloseModelAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance pureModelCloseModelMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance pureModelCloseModelLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance pureModelCloseModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem pureBindTerm_model (k t : M) : pureBindTerm k t = bindTerm k t := rfl
theorem pureBindPair_model (k v : M) : pureBindPair k v = bindPair k v := rfl
theorem pureFormulaCloseConstruction_model :
    (pureFormulaCloseConstruction (V := M)) = FormulaClose.construction := by
  rfl
theorem pureCloseIterConstruction_model :
    (pureCloseIterConstruction (V := M)) = closeIterConstruction := by
  rfl
theorem pureModelClose_model (n p : M) : pureModelClose n p = modelClose n p := by
  rfl
#print axioms pureModelClose_model
end models
end PA194BindSource
