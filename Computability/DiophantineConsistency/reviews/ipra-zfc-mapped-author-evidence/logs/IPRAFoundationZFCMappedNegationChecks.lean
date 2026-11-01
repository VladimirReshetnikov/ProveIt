import DiophantineConsistency.IPRAFoundationZFCMappedNegation

noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat
open DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.IPRAFoundationZFCMappedNegation

example {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}
    (f : ℒₒᵣ →ᵥ L) (hb : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 ∼∼mappedNativeRefutation f) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f :=
  mappedZFCConsistencyEquivalent f hb

#print axioms DiophantineConsistency.IPRAFoundationZFCMappedNegation.mappedZFCConsistencyEquivalent
