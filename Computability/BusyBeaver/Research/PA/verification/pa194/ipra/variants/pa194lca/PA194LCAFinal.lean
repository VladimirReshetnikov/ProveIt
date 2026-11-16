import PA194LCACoverage
import PA194LCANative
set_option autoImplicit false
namespace PA194LCAFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCAData.table 194 :=
  PA194LCANative.consistency_iff_literal_nonhalt PA194LCACoverage.checked

#print axioms consistency_iff_literal_nonhalt
end PA194LCAFinal
