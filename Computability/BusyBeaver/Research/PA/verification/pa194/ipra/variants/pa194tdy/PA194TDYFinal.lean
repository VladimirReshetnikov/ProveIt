import PA194TDYNative
import PA194TDYCoverageAll

set_option autoImplicit false

namespace PA194TDYFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

noncomputable def haltSentence := machineHaltSentence PA194TDYData.table 194

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194TDYNative.consistency_iff_literal_nonhalt PA194TDYCoverageAll.checked

#print axioms consistency_iff_literal_nonhalt
end PA194TDYFinal
