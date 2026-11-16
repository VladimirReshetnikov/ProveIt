import PA194LCFastRows
import PA194FastController
import PA194LCNative
import PA194LCCoverage

set_option autoImplicit false

namespace PA194LCFastNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

noncomputable def haltSentence := machineHaltSentence PA194LCFastRows.table 194

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194FastController.consistency_iff PA194LCFastRows.certificate
    (PA194LCNative.sameSourceHalt PA194LCCoverage.checked)

#print axioms consistency_iff_literal_nonhalt
end PA194LCFastNative
