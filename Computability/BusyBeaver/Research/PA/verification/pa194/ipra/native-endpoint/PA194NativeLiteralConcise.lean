import PA194NativeLiteralFinal
import IPRABridge

set_option autoImplicit false

namespace PA194NativeLiteralConcise
open LO LO.FirstOrder LO.Entailment LeanProofs.ConciseIPRA
open DiophantineConsistency.IPRAPA196Consistency
open scoped Fm LO.FirstOrder

/-- The primary PA194 endpoint, with the existing PA refutation and literal
    halting predicates translated into the ConciseIPRA object language. -/
noncomputable def sentence : Fm PTm 0 :=
  IPRABridge.toConciseSentence (nativePAConsistency 🡘 ∼PA194ExplicitEndpoint.haltSentence)

theorem consistency_iff_literal_nonhalt : ([] : List (Fm PTm 0)) ⊢[PRAAx] sentence := by
  unfold sentence
  apply IPRABridge.standardToConcise
  exact PA194NativeLiteralFinal.consistency_iff_literal_nonhalt

#print axioms consistency_iff_literal_nonhalt
end PA194NativeLiteralConcise
