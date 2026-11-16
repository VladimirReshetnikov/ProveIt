import PA194LCAX11HRelativeNative
import PA194AX11HFinal
set_option autoImplicit false
namespace PA194LCAX11HConditionalFinal
open LO LO.Entailment
open DiophantineConsistency.IPRAStandardTheory DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint

theorem consistency_iff_literal_nonhalt (coverage : PA194LCAX11HChecks.AllContracts) :
    standardTheory ⊢ nativePAConsistency 🡘 ∼machineHaltSentence PA194LCAX11HData.table 194 := by
  have a := Classical.choice PA194AX11HFinal.consistency_iff_literal_nonhalt
  have b := Classical.choice (PA194LCAX11HRelativeNative.relative_nonhalt coverage)
  exact ⟨K_intro (C_trans (K_left a) (K_left b)) (C_trans (K_right b) (K_right a))⟩
#print axioms consistency_iff_literal_nonhalt
end PA194LCAX11HConditionalFinal
