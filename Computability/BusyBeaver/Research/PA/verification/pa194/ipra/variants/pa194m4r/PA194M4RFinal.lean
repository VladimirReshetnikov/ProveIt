import PA194M4RCoverage
import PA194M4RNative
set_option autoImplicit false
namespace PA194M4RFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194M4RData.table 194 :=
  PA194M4RNative.consistency_iff_literal_nonhalt PA194M4RCoverage.checked

#print axioms consistency_iff_literal_nonhalt
end PA194M4RFinal
