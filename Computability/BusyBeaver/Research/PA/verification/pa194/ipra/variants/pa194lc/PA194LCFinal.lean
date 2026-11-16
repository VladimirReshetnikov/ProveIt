import PA194LCCoverage
import PA194LCNative

set_option autoImplicit false

namespace PA194LCFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCData.table 194 :=
  PA194LCNative.consistency_iff_literal_nonhalt PA194LCCoverage.checked

#print axioms consistency_iff_literal_nonhalt
end PA194LCFinal
