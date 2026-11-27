import PA194LCAX11HConditionalFinal
import PA194LCAX11HCoverage
set_option autoImplicit false
namespace PA194LCAX11HFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCAX11HData.table 194 :=
  PA194LCAX11HConditionalFinal.consistency_iff_literal_nonhalt PA194LCAX11HCoverage.checked

#print axioms consistency_iff_literal_nonhalt
end PA194LCAX11HFinal
