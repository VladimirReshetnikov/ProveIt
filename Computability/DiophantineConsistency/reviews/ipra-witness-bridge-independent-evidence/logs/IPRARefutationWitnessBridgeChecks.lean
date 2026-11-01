import DiophantineConsistency.IPRARefutationWitnessBridge

open LO LO.FirstOrder
open scoped LO.FirstOrder
open DiophantineConsistency.IPRANativeFormula DiophantineConsistency.IPRARefutationWitnessBridge

example {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}
    (ρ bound : Sentence L) (h₁ : T ⊢! ρᴺ 🡒 boundᴺ)
    (h₂ : T ⊢! boundᴺ 🡒 ∼∼native bound) (h₃ : T ⊢! native bound 🡒 native ρ) :
    T ⊢! (∼ρ)ᴺ 🡘 ∼native ρ := negationOfWitness ρ bound h₁ h₂ h₃

#print axioms DiophantineConsistency.IPRARefutationWitnessBridge.backwardOfWitness
#print axioms DiophantineConsistency.IPRARefutationWitnessBridge.negationOfWitness
