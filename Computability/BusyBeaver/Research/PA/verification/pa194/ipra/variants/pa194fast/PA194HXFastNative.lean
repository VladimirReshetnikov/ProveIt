import PA194HXFastRows
import PA194FastController
import PA194HXNative
import PA194HXCoverageAll

set_option autoImplicit false

namespace PA194HXFastNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

noncomputable def haltSentence := machineHaltSentence PA194HXFastRows.table 194

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194FastController.consistency_iff PA194HXFastRows.certificate
    (PA194HXNative.sameSourceHalt PA194HXCoverageAll.checked)

#print axioms consistency_iff_literal_nonhalt
end PA194HXFastNative
