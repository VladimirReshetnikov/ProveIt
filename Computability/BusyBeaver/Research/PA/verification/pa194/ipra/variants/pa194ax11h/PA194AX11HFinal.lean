import PA194AX11HDirectNative
import PA194AX11HReturningCommands
import PA194AX11HHaltFrame
import PA194AX11HAXFrame
import PA194AX11HBodyRowsAll

set_option autoImplicit false

namespace PA194AX11HFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem commandContracts : PA194AX11HDirectNative.CommandContracts := by
  intro M _ _ _ _
  dsimp only
  intro _
  exact ⟨PA194AX11HReturningCommands.advance (M := M)
    (PA194AX11HAXFrame.advance PA194AX11HBodyRowsAll.agreement),
    PA194AX11HHaltFrame.fromFlag (M := M)⟩

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194AX11HData.table 194 :=
  PA194AX11HDirectNative.consistency_iff_literal_nonhalt commandContracts

#print axioms commandContracts
#print axioms consistency_iff_literal_nonhalt
end PA194AX11HFinal
