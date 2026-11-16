import PA194SELHalting
import PA194VariantNative

set_option autoImplicit false

namespace PA194SELNative
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

/-- The canonical arithmetic halting sentence of the delivered PA194SEL table. -/
noncomputable def haltSentence := machineHaltSentence PA194SELSimulation.variantTable 194

/-- A derivation in standard iPRA for the literal PA194SEL machine. -/
theorem consistency_iff_literal_nonhalt :
    standardTheory ⊢ nativePAConsistency 🡘 ∼haltSentence :=
  PA194VariantNative.consistency_iff_nonhalt PA194SELSimulation.variantTable 194
    (fun V _ _ => (PA194SELSimulation.haltRuns (V := V)).symm)

#print axioms consistency_iff_literal_nonhalt
end PA194SELNative
