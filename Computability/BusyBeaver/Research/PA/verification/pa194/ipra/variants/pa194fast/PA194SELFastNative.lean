import PA194SELFastRows
import PA194SELHalting
import PA194VariantNative

set_option autoImplicit false

namespace PA194SELFastNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

noncomputable def haltSentence := machineHaltSentence PA194SELFastRows.table 194

theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194VariantNative.consistency_iff_nonhalt PA194SELFastRows.table 194
    (fun V _ _ => (PA194SELSimulation.haltRuns (V := V)).symm.trans
      (PA194GuardedShortcuts.sameHalt (V := V) PA194SELFastRows.certificate))

#print axioms consistency_iff_literal_nonhalt
end PA194SELFastNative
