import PA194LCBInitializer
import PA194ControllerNative
set_option autoImplicit false
namespace PA194LCBNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open PA194TrieSourceController (AllContracts)
open PA194LCBController (data)

theorem sameSourceHalt (checks : AllContracts data) :
    PA194ControllerNative.SameSourceHalt PA194LCBData.table 194 := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact PA194LCBController.halt_iff_controller (M := M) checks _ PA194LCBInitializer.startup_root

/-- A finite source check suffices for the complete LC_B consistency derivation. -/
theorem consistency_iff_literal_nonhalt (checks : AllContracts data) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCBData.table 194 :=
  PA194ControllerNative.consistency_iff PA194LCBData.table 194 (sameSourceHalt checks)

#print axioms sameSourceHalt
#print axioms consistency_iff_literal_nonhalt
end PA194LCBNative
