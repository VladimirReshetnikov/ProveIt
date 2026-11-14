import PA194DistinctGateEndpoint
import PA194DistinctGateNumeric
set_option autoImplicit false
set_option maxHeartbeats 5000000
namespace PA194ModeledHaltRefutesPA
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

theorem modeled_halt_refutes_PA (k : M) (hh : F haltAfter ![k] = 1) :
    Provable (𝗣𝗔 : ArithmeticTheory) (^⊥ : M) := by
  apply PA194DistinctGateEndpoint.modeled_halt_refutes_PA_of_distinct_tail ?_ k hh
  intro a b c hab hca hcb
  exact PA194DistinctGateNumeric.distinct_gate_tail a b c hab hca hcb
#print axioms modeled_halt_refutes_PA
end models
end PA194ModeledHaltRefutesPA
