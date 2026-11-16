import PA194LCController
import PA194ControllerNative
set_option autoImplicit false
namespace PA194LCNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open PA194LCController (AllContracts)

theorem sameSourceHalt (checks : AllContracts) :
    PA194ControllerNative.SameSourceHalt PA194LCData.table 194 := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact PA194LCController.halt_iff_controller (M := M) checks
    (PA194LCController.literalBoxes (PA194CompressedStartup.initialSpare (M := M)))

/-- A finite source check suffices for the complete LC consistency derivation. -/
theorem consistency_iff_literal_nonhalt (checks : AllContracts) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCData.table 194 :=
  PA194ControllerNative.consistency_iff PA194LCData.table 194 (sameSourceHalt checks)

#print axioms sameSourceHalt
#print axioms consistency_iff_literal_nonhalt
end PA194LCNative
