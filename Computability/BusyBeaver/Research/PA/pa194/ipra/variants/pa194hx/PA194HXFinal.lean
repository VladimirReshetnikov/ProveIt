import PA194HXCoverageAll
import PA194HXNative

set_option autoImplicit false

namespace PA194HXFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194HXDispatch.table 194 :=
  PA194HXNative.consistency_iff_literal_nonhalt PA194HXCoverageAll.checked

#print axioms consistency_iff_literal_nonhalt
end PA194HXFinal
