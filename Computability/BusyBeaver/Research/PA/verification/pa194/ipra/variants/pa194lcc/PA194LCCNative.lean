import PA194LCCInitializer
import PA194ControllerNative
set_option autoImplicit false
namespace PA194LCCNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open PA194TrieSourceController (AllContracts)
open PA194LCCController (data)

theorem sameSourceHalt (checks : AllContracts data) :
    PA194ControllerNative.SameSourceHalt PA194LCCData.table 194 := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact PA194LCCController.halt_iff_controller (M := M) checks _ PA194LCCInitializer.startup_root

/-- A finite source check suffices for the complete LC consistency derivation. -/
theorem consistency_iff_literal_nonhalt (checks : AllContracts data) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCCData.table 194 :=
  PA194ControllerNative.consistency_iff PA194LCCData.table 194 (sameSourceHalt checks)

#print axioms sameSourceHalt
#print axioms consistency_iff_literal_nonhalt
end PA194LCCNative
