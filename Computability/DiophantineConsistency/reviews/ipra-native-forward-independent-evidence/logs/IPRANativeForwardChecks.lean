import DiophantineConsistency.IPRANativeForwardTheory

open LO LO.FirstOrder
open scoped LO.FirstOrder
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRANativeForwardTheory

example {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}
    (φ : Sentence L) : T ⊢! native φ 🡒 φᴺ := theoryNativeForward φ

#print axioms DiophantineConsistency.IPRANativeForward.nativeForward
#print axioms DiophantineConsistency.IPRANativeForwardTheory.theoryNativeForward
