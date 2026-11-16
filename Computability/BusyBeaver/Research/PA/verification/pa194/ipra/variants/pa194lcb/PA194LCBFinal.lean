import PA194LCBCoverage
import PA194LCBNative
set_option autoImplicit false
namespace PA194LCBFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCBData.table 194 :=
  PA194LCBNative.consistency_iff_literal_nonhalt PA194LCBCoverage.checked

#print axioms consistency_iff_literal_nonhalt
end PA194LCBFinal
