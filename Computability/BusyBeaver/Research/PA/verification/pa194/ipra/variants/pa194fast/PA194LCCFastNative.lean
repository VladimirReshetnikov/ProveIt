import PA194LCCFastRows
import PA194FastController
import PA194LCCNative

set_option autoImplicit false

namespace PA194LCCFastNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

noncomputable def haltSentence := machineHaltSentence PA194LCCFastRows.table 194

theorem consistency_iff_literal_nonhalt (checks : PA194TrieSourceController.AllContracts PA194LCCController.data) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194FastController.consistency_iff PA194LCCFastRows.certificate
    (PA194LCCNative.sameSourceHalt checks)

#print axioms consistency_iff_literal_nonhalt
end PA194LCCFastNative
