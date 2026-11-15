import PA194ModelNumericalSeedRefutation
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
local instance genericNumericalHaltZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance genericNumericalHaltOne : One M := ⟨F oneCode Fin.elim0⟩
local instance genericNumericalHaltAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance genericNumericalHaltMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance genericNumericalHaltLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance genericNumericalHaltIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A uniform internal axiom supplier makes any internal source refutation halt
    the modeled scheduler. -/
theorem numericalSeed_provable_halts (T : Theory SourceL) [T.Δ₁]
    (axiomRule : ∀ reserve e s p : M, SeedAdmission 0 reserve e (axm s p) → p ∈ T.Δ₁Class →
      numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1))
    (h : Provable T (^⊥ : M)) : ∃ k : M, F haltAfter ![k] = 1 := by
  obtain ⟨d,hd⟩ := h
  exact PA194ModelFairness.provable_halts (numericalSeed_refutation_target T d hd axiomRule)

theorem numericalSeed_consistent_of_nonhalting (T : Theory SourceL) [T.Δ₁]
    (axiomRule : ∀ reserve e s p : M, SeedAdmission 0 reserve e (axm s p) → p ∈ T.Δ₁Class →
      numericalQuant.Pr (numericalQuant.imp (numericalTranslation.tr e p) 1))
    (hnh : ∀ k : M, F haltAfter ![k] ≠ 1) : ¬ Provable T (^⊥ : M) := by
  intro h
  obtain ⟨k,hk⟩ := numericalSeed_provable_halts T axiomRule h
  exact hnh k hk

#print axioms numericalSeed_provable_halts
#print axioms numericalSeed_consistent_of_nonhalting
end models
end PA194ModelLogic
