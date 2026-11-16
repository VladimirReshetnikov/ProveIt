import PA194LCCFastNative
import PA194LCCCoverage

set_option autoImplicit false

namespace PA194LCCFastFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼PA194LCCFastNative.haltSentence :=
  PA194LCCFastNative.consistency_iff_literal_nonhalt PA194LCCCoverage.checked

#print axioms consistency_iff_literal_nonhalt
end PA194LCCFastFinal
