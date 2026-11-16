import PA194C32SourceEndpoint
import PA194ControllerNative

set_option autoImplicit false

namespace PA194C32Native
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open PA194C32SourceEndpoint (Covered)

theorem sameSourceHalt (checks : Covered) :
    PA194ControllerNative.SameSourceHalt PA194C32Data.table 194 := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact PA194C32SourceEndpoint.endpoint (M := M) checks

/-- Finite source checks suffice for the C32 consistency derivation. -/
theorem consistency_iff_literal_nonhalt (checks : Covered) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194C32Data.table 194 :=
  PA194ControllerNative.consistency_iff PA194C32Data.table 194 (sameSourceHalt checks)

#print axioms consistency_iff_literal_nonhalt
end PA194C32Native
