import DiophantineConsistency.IPRARefutationNegationTheory

open LO LO.FirstOrder
open scoped LO.FirstOrder
open DiophantineConsistency.IPRARefutationNegationTheory

example {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}
    (ρ : Sentence L) (ordinary : Sentenceᵢ L)
    (hf : T ⊢! ordinary 🡒 ρᴺ) (hb : T ⊢! ρᴺ 🡒 ∼∼ordinary) :
    T ⊢! (∼ρ)ᴺ 🡘 ∼ordinary := theoryTranslatedNegationEquivalent ρ ordinary hf hb

#print axioms DiophantineConsistency.IPRARefutationNegationTheory.theoryNegationsEquivalent
#print axioms DiophantineConsistency.IPRARefutationNegationTheory.theoryTranslatedNegationEquivalent
