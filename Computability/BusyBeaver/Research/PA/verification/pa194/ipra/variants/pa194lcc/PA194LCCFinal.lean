import PA194LCCCoverage
import PA194LCCNative
set_option autoImplicit false
namespace PA194LCCFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCCData.table 194 :=
  PA194LCCNative.consistency_iff_literal_nonhalt PA194LCCCoverage.checked

#print axioms consistency_iff_literal_nonhalt
end PA194LCCFinal
