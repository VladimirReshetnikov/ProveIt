import PA1944LInitializer
import PA194ControllerNative
set_option autoImplicit false
namespace PA1944LNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open PA194TrieSourceController (AllContracts)
open PA1944LController (data)

theorem sameSourceHalt (checks : AllContracts data) :
    PA194ControllerNative.SameSourceHalt PA1944LData.table 194 := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact PA1944LController.halt_iff_controller (M := M) checks _ PA1944LInitializer.startup_root

/-- A finite source check suffices for the complete 4L consistency derivation. -/
theorem consistency_iff_literal_nonhalt (checks : AllContracts data) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LData.table 194 :=
  PA194ControllerNative.consistency_iff PA1944LData.table 194 (sameSourceHalt checks)

#print axioms sameSourceHalt
#print axioms consistency_iff_literal_nonhalt
end PA1944LNative
