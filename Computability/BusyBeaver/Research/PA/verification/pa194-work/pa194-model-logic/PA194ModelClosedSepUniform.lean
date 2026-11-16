import PA194ModelSepRootGraph
import PA194ModelClosedSepClassifier
import PA194ModelSeedEnvironment
import PA194ModelNumericalSeedRefutation

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
local instance closedSepUniformModelZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance closedSepUniformModelOne : One M := ⟨F oneCode Fin.elim0⟩
local instance closedSepUniformModelAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance closedSepUniformModelMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance closedSepUniformModelLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance closedSepUniformModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- The arithmetic-only constructor is definitionally the PA194 model constructor. -/
theorem sepRootPure_model (p : M) : sepRootPure p = sepRoot p := by
  simp [sepRootPure,sepRoot,sepInner,relExtVector,adjoin_def]

/-- The same fixed arithmetic formula recognizes the model's code predicate. -/
theorem closedSepUniform_model (q : M) : M ⊧/![q] closedSepUniform.val ↔ closedSepCode q := by
  letI : 𝚫₁-Predicate (closedSepPure : M → Prop) via closedSepUniform := closedSepUniform_defined
  have hv : M ⊧/![q] closedSepUniform.val ↔ closedSepPure q := by
    simpa using (HierarchySymbol.Defined.iff (φ := closedSepUniform) (v := ![q]))
  rw [hv]
  simp only [closedSepPure,closedSepCode,sepRootPure_model]
  simp only [and_assoc]

#print axioms sepRootPure_model
#print axioms closedSepUniform_model
end models
end PA194ModelLogic
