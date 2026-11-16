import PA194TDYSourceEndpoint
import PA194ControllerNative

set_option autoImplicit false

namespace PA194TDYNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open PA194TDYSourceEndpoint (Covered)

theorem sameSourceHalt (checks : Covered) :
    PA194ControllerNative.SameSourceHalt PA194TDYData.table 194 := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact PA194TDYSourceEndpoint.endpoint (M := M) checks

/-- Finite source checks suffice for the TDY consistency derivation. -/
theorem consistency_iff_literal_nonhalt (checks : Covered) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194TDYData.table 194 :=
  PA194ControllerNative.consistency_iff PA194TDYData.table 194 (sameSourceHalt checks)

#print axioms consistency_iff_literal_nonhalt
end PA194TDYNative
