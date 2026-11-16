import PA194P5Native
import PA194P5CoverageAll

set_option autoImplicit false

namespace PA194P5Final
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

noncomputable def haltSentence := machineHaltSentence PA194P5Data.table 194

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194P5Native.consistency_iff_literal_nonhalt PA194P5CoverageAll.checked

#print axioms consistency_iff_literal_nonhalt
end PA194P5Final
