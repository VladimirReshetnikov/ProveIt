import PA194P5SourceEndpoint
import PA194ControllerNative

set_option autoImplicit false

namespace PA194P5Native
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open PA194P5SourceEndpoint (Covered)

theorem sameSourceHalt (checks : Covered) :
    PA194ControllerNative.SameSourceHalt PA194P5Data.table 194 := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact PA194P5SourceEndpoint.endpoint (M := M) checks

/-- A finite source check suffices for the complete P5 consistency derivation. -/
theorem consistency_iff_literal_nonhalt (checks : Covered) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194P5Data.table 194 :=
  PA194ControllerNative.consistency_iff PA194P5Data.table 194 (sameSourceHalt checks)

#print axioms consistency_iff_literal_nonhalt
end PA194P5Native
