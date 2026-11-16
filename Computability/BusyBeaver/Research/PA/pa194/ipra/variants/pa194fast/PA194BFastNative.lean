import PA194BFastRows
import PA194BHalting
import PA194VariantNative

set_option autoImplicit false

namespace PA194BFastNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

noncomputable def haltSentence := machineHaltSentence PA194BFastRows.table 194

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194VariantNative.consistency_iff_nonhalt PA194BFastRows.table 194
    (fun V _ _ => (PA194BSimulation.haltRuns (V := V)).symm.trans
      (PA194GuardedShortcuts.sameHalt (V := V) PA194BFastRows.certificate))

#print axioms consistency_iff_literal_nonhalt
end PA194BFastNative
