import PA194FastSegment
import PA194VariantNative

set_option autoImplicit false

namespace PA194FastNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

/-- The arithmetic halting sentence of the pinned, two-shortcut literal
    primary_fast table, expressed in the primary dense numbering. -/
noncomputable def haltSentence := machineHaltSentence PA194FastRows.table 194

/-- The direct bounded stuttering reduction yields a derivation in iPRA. -/
theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194VariantNative.consistency_iff_nonhalt PA194FastRows.table 194
    (fun V _ _ => PA194FastSegment.sameHalt (V := V))

#print axioms consistency_iff_literal_nonhalt
end PA194FastNative
