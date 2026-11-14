import PA194SchedulerHaltCode
import PA194EqualGateNumeric
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 5000000
namespace PA194DistinctGateEndpoint
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
  PA194TargetGate PA194SourceLineSoundness PA194SchedulerHaltCode
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem all_tail_from_distinct
    (htail : ∀ a b c : M, a ≠ b → c ≠ a → c ≠ b →
      good (PA194SourceGateReduction.gateNeg (separationTailValue a b c))) :
    ∀ a b c : M, c ≠ a → c ≠ b →
      good (PA194SourceGateReduction.gateNeg (separationTailValue a b c)) := by
  intro a b c ha hb
  by_cases hab : a = b
  · subst a
    have h := PA194EqualGateNumeric.equal_gate_tail b c hb
    rw [PA194SourceGateTargetLink.gate_tail_eq] at h
    exact h
  · exact htail a b c hab ha hb

theorem modeled_halt_refutes_PA_of_distinct_tail
    (htail : ∀ a b c : M, a ≠ b → c ≠ a → c ≠ b →
      good (PA194SourceGateReduction.gateNeg (separationTailValue a b c)))
    (k : M) (hh : F haltAfter ![k] = 1) : Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) :=
  PA194SchedulerHaltCode.modeled_halt_refutes_PA_of_tail (all_tail_from_distinct htail) k hh
#print axioms all_tail_from_distinct
#print axioms modeled_halt_refutes_PA_of_distinct_tail
end models
end PA194DistinctGateEndpoint
