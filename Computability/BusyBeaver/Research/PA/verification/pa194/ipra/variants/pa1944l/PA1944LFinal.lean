import PA1944LCoverage
import PA1944LNative
set_option autoImplicit false
namespace PA1944LFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA1944LData.table 194 :=
  PA1944LNative.consistency_iff_literal_nonhalt PA1944LCoverage.checked

#print axioms consistency_iff_literal_nonhalt
end PA1944LFinal
