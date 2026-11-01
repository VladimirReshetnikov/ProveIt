import DiophantineConsistency.IPRAFoundationZFCWitnessBound

noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.FoundationZFCConsistencyNat
open DiophantineConsistency.FoundationHAConsistencyNormalization
open DiophantineConsistency.IPRANativeFormula
open DiophantineConsistency.IPRAFoundationZFCMappedNegation
open DiophantineConsistency.IPRAFoundationZFCWitnessBound

example {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}
    (f : ℒₒᵣ →ᵥ L)
    (h₁ : T ⊢! (Semiformula.lMap f rho)ᴺ 🡒 (Semiformula.lMap f boundedRefutation)ᴺ)
    (h₂ : T ⊢! (Semiformula.lMap f boundedRefutation)ᴺ 🡒 ∼∼native (Semiformula.lMap f boundedRefutation))
    (h₃ : T ⊢! native (Semiformula.lMap f boundedRefutation) 🡒 native (Semiformula.lMap f rho)) :
    T ⊢! (Semiformula.lMap f sourceSentence)ᴺ 🡘 ∼mappedNativeRefutation f :=
  mappedZFCNegationOfBound f h₁ h₂ h₃

#print axioms DiophantineConsistency.IPRAFoundationZFCWitnessBound.boundedMatrix_isDeltaZero
#print axioms DiophantineConsistency.IPRAFoundationZFCWitnessBound.mappedZFCNegationOfBound
