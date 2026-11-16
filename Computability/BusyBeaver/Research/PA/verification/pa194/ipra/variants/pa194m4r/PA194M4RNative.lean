import PA194M4RInitializer
import PA194ControllerNative
set_option autoImplicit false
namespace PA194M4RNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open PA194TrieSourceController (AllContracts)
open PA194M4RController (data)

theorem sameSourceHalt (checks : AllContracts data) :
    PA194ControllerNative.SameSourceHalt PA194M4RData.table 194 := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact PA194M4RController.halt_iff_controller (M := M) checks _ PA194M4RInitializer.startup_root

/-- A finite source check suffices for the complete PA194M4R consistency derivation. -/
theorem consistency_iff_literal_nonhalt (checks : AllContracts data) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194M4RData.table 194 :=
  PA194ControllerNative.consistency_iff PA194M4RData.table 194 (sameSourceHalt checks)

#print axioms sameSourceHalt
#print axioms consistency_iff_literal_nonhalt
end PA194M4RNative
