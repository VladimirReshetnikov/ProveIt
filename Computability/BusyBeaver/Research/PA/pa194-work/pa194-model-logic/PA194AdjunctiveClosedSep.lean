import PA194ClosedSepTheoryModel
import PA194ModelClosedSepUniform
import PA194ModelFairness
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
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable PA194SchedulerHaltCode
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
/-- Finite adjunctive axioms together with classifier-defined closed separation. -/
noncomputable def adjunctiveClosedSepTheory : Theory SourceL :=
  adjunctiveTheory ∪ closedSepTheory

@[implicit_reducible] noncomputable def adjunctiveClosedSepTheoryDelta : adjunctiveClosedSepTheory.Δ₁ := by
  letI := adjunctiveTheoryDelta
  letI := closedSepTheoryDelta
  exact Theory.Δ₁.add adjunctiveTheoryDelta closedSepTheoryDelta

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance adjunctiveClosedSepModelZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance adjunctiveClosedSepModelOne : One M := ⟨F oneCode Fin.elim0⟩
local instance adjunctiveClosedSepModelAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance adjunctiveClosedSepModelMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance adjunctiveClosedSepModelLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance adjunctiveClosedSepModelIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






theorem adjunctiveClosedSepTheory_class (p : M) :
    letI := adjunctiveClosedSepTheoryDelta
    letI := adjunctiveTheoryDelta
    p ∈ adjunctiveClosedSepTheory.Δ₁Class ↔
      p ∈ adjunctiveTheory.Δ₁Class ∨ closedSepCode p := by
  letI := adjunctiveTheoryDelta
  letI := closedSepTheoryDelta
  letI := adjunctiveClosedSepTheoryDelta
  change M ⊧/![p] (adjunctiveTheory.Δ₁ch ⋎ closedSepTheory.Δ₁ch).val ↔ _
  have hcases :
      M ⊧/![p] (adjunctiveTheory.Δ₁ch ⋎ closedSepTheory.Δ₁ch).val ↔
      (M ⊧/![p] adjunctiveTheory.Δ₁ch.val) ∨ (M ⊧/![p] closedSepTheory.Δ₁ch.val) := by
    simp only [HierarchySymbol.Semiformula.val_or, LogicalConnective.HomClass.map_or, LogicalConnective.Prop.or_eq]
  rw [hcases]
  exact or_congr Iff.rfl (closedSepTheory_class p)

theorem adjunctiveClosedSep_refutation_target (d : M)
    (hd : letI := adjunctiveClosedSepTheoryDelta; Proof adjunctiveClosedSepTheory d (^⊥ : M)) :
    TargetProvable (1 : M) := by
  letI := adjunctiveClosedSepTheoryDelta
  apply closedSepClassification_refutation_target adjunctiveClosedSepTheory d
  · intro p hp
    exact (adjunctiveClosedSepTheory_class p).mp hp
  · exact hd

theorem adjunctiveClosedSep_provable_halts
    (h : letI := adjunctiveClosedSepTheoryDelta; Provable adjunctiveClosedSepTheory (^⊥ : M)) :
    ∃ k : M, F haltAfter ![k] = 1 := by
  letI := adjunctiveClosedSepTheoryDelta
  obtain ⟨d,hd⟩ := h
  exact PA194ModelFairness.provable_halts (adjunctiveClosedSep_refutation_target d hd)

theorem adjunctiveClosedSep_consistent_of_nonhalting
    (hnh : ∀ k : M, F haltAfter ![k] ≠ 1) :
    letI := adjunctiveClosedSepTheoryDelta; ¬ Provable adjunctiveClosedSepTheory (^⊥ : M) := by
  letI := adjunctiveClosedSepTheoryDelta
  intro h
  obtain ⟨k,hk⟩ := adjunctiveClosedSep_provable_halts h
  exact hnh k hk

#print axioms adjunctiveClosedSepTheoryDelta
#print axioms adjunctiveClosedSepTheory_class
#print axioms adjunctiveClosedSep_refutation_target
#print axioms adjunctiveClosedSep_provable_halts
#print axioms adjunctiveClosedSep_consistent_of_nonhalting
end models
end PA194ModelLogic
