import PA1944LFinal
import IPRABridge.Standard

/-! The exact 4L table's PA consistency equivalence in ordinary ConciseIPRA. -/

set_option autoImplicit false

namespace PA1944LConcise

open LO LO.FirstOrder LeanProofs.ConciseIPRA
open DiophantineConsistency.IPRAPA196Consistency
open ConPA.MachineEndpoint
open scoped Fm LO.FirstOrder

/-- Retain the Foundation PA refutation predicate and the literal 4L
blank-input halting predicate under the checked translation. -/
noncomputable def sentence : Fm PTm 0 :=
  IPRABridge.toConciseSentence
    (nativePAConsistency 🡘 ∼machineHaltSentence PA1944LData.table 194)

theorem consistency_iff_literal_nonhalt : ([] : List (Fm PTm 0)) ⊢[PRAAx] sentence :=
  IPRABridge.standardToConcise PA1944LFinal.consistency_iff_literal_nonhalt

#print axioms consistency_iff_literal_nonhalt

end PA1944LConcise
