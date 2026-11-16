import PA194C32Native
import PA194C32CoverageAll

set_option autoImplicit false

namespace PA194C32Final
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

noncomputable def haltSentence := machineHaltSentence PA194C32Data.table 194

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194C32Native.consistency_iff_literal_nonhalt PA194C32CoverageAll.checked

#print axioms consistency_iff_literal_nonhalt
end PA194C32Final
