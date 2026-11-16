import PA194ADControllerEndpoint
import PA194ControllerNative

set_option autoImplicit false

namespace PA194ADNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open PA194ADController (AllContracts)

theorem sameSourceHalt (checks : AllContracts) :
    PA194ControllerNative.SameSourceHalt PA194ADCompressedData.table 194 := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact PA194ADControllerEndpoint.halt_iff_controller_literal (M := M) checks

/-- A finite source check suffices for the complete AD consistency derivation. -/
theorem consistency_iff_literal_nonhalt (checks : AllContracts) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194ADCompressedData.table 194 :=
  PA194ControllerNative.consistency_iff PA194ADCompressedData.table 194 (sameSourceHalt checks)

#print axioms consistency_iff_literal_nonhalt
end PA194ADNative
