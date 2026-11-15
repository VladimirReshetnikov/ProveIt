import PA194ClosedSepTheoryInstance
import PA194ModelClosedSepUniform
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
local instance closedSepTheoryModelZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance closedSepTheoryModelOne : One M := ⟨F oneCode Fin.elim0⟩
local instance closedSepTheoryModelAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance closedSepTheoryModelMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance closedSepTheoryModelLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance closedSepTheoryModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- Exact internal class for the classifier-defined standard theory. -/
theorem closedSepTheory_class (q : M) :
    letI := closedSepTheoryDelta
    q ∈ closedSepTheory.Δ₁Class ↔ closedSepCode q := by
  letI := closedSepTheoryDelta
  change M ⊧/![q] closedSepUniform.val ↔ closedSepCode q
  exact closedSepUniform_model q

/-- Transport a refutation of the classifier-defined separation theory. -/
theorem closedSepTheory_refutation_target (d : M)
    (hd : letI := closedSepTheoryDelta; Proof closedSepTheory d (^⊥ : M)) :
    TargetProvable (1 : M) := by
  letI := closedSepTheoryDelta
  apply closedSepClassification_refutation_target closedSepTheory d
  · intro p hp
    exact Or.inr ((closedSepTheory_class p).mp hp)
  · exact hd

#print axioms closedSepTheory_class
#print axioms closedSepTheory_refutation_target
end models
end PA194ModelLogic
