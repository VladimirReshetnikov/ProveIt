import PA194ADFastRows
import PA194FastController
import PA194ADNative
import PA194ADCoverage

set_option autoImplicit false

namespace PA194ADFastNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

noncomputable def haltSentence := machineHaltSentence PA194ADFastRows.table 194

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194FastController.consistency_iff PA194ADFastRows.certificate
    (PA194ADNative.sameSourceHalt PA194ADCoverage.checked)

#print axioms consistency_iff_literal_nonhalt
end PA194ADFastNative
