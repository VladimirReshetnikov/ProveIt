import PA194ModelAdjunctiveRefutation
import PA194ModelFairness

/-! General target witness and seeded existential-introduction rule. -/
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
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance finiteAdjunctiveHaltZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance finiteAdjunctiveHaltOne : One M := ⟨F oneCode Fin.elim0⟩
local instance finiteAdjunctiveHaltAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance finiteAdjunctiveHaltMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance finiteAdjunctiveHaltLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance finiteAdjunctiveHaltIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- An internal finite-adjunctive refutation makes the modeled scheduler halt. -/
theorem finiteAdjunctive_provable_halts
    (h : letI := adjunctiveTheoryDelta; Provable adjunctiveTheory (^⊥ : M)) :
    ∃ k : M, F haltAfter ![k] = 1 := by
  letI := adjunctiveTheoryDelta
  obtain ⟨d,hd⟩ := h
  exact PA194ModelFairness.provable_halts (finiteAdjunctive_refutation_target d hd)

/-- Nonhalting of the modeled scheduler implies consistency of the finite source theory. -/
theorem finiteAdjunctive_consistent_of_nonhalting
    (hnh : ∀ k : M, F haltAfter ![k] ≠ 1) :
    letI := adjunctiveTheoryDelta; ¬ Provable adjunctiveTheory (^⊥ : M) := by
  letI := adjunctiveTheoryDelta
  intro h
  obtain ⟨k,hk⟩ := finiteAdjunctive_provable_halts h
  exact hnh k hk

#print axioms finiteAdjunctive_provable_halts
#print axioms finiteAdjunctive_consistent_of_nonhalting
end models
end PA194ModelLogic
