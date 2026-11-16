import PA194ADCoverage
import PA194ADNative

set_option autoImplicit false

namespace PA194ADFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194ADCompressedData.table 194 :=
  PA194ADNative.consistency_iff_literal_nonhalt PA194ADCoverage.checked

#print axioms consistency_iff_literal_nonhalt
end PA194ADFinal
