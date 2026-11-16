import PA194ModelRelExtReference
import PA194ModelFormulaTranslation
import PA194RelExtTypedTranslation

/-! Coded Foundation membership relation-extensionality syntax in an arbitrary
candidate-PRA model. -/
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
local instance relExtRootBoundZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance relExtRootBoundOne : One M := ⟨F oneCode Fin.elim0⟩
local instance relExtRootBoundAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance relExtRootBoundMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance relExtRootBoundLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance relExtRootBoundIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A stronger compiler-style reserve bound implies the four-label freshness budget. -/
theorem fixedFormulaTranslation_relExt_target_rootBound
    (initial free base reserve : M)
    (hz : base + (⌜PA194RelExtTypedTranslation.sourceRelExt⌝ : M) ≤ reserve) :
    TargetProvable (F fixedFormulaTranslation
      ![(⌜PA194RelExtTypedTranslation.sourceRelExt⌝ : M),initial,free,base,reserve]) := by
  apply fixedFormulaTranslation_relExt_target
  rw [relExtRoot_quote] at hz
  have h := add_le_add_right (relExtRoot_four_le (M := M)) base
  have h4 : ((((base+1)+1)+1)+1) ≤ base + relExtRoot := by
    simpa only [zero_add, add_assoc, add_comm, add_left_comm] using h
  exact le_trans h4 hz

#print axioms fixedFormulaTranslation_relExt_target_rootBound
end models
end PA194ModelLogic
