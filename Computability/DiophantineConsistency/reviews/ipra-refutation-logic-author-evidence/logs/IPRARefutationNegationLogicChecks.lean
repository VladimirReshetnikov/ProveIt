import DiophantineConsistency.IPRARefutationNegationLogic

open LO LO.FirstOrder
open scoped LO.FirstOrder
open DiophantineConsistency.IPRARefutationNegationLogic

example {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} (ρ : Proposition L)
    (ordinary : Propositionᵢ L) (hforward : Λ ⊢! ordinary 🡒 ρᴺ)
    (hbackward : Λ ⊢! ρᴺ 🡒 ∼∼ordinary) :
    Λ ⊢! (∼ρ)ᴺ 🡘 ∼ordinary :=
  translatedNegationEquivalent ρ ordinary hforward hbackward

#print axioms DiophantineConsistency.IPRARefutationNegationLogic.negationsEquivalent
#print axioms DiophantineConsistency.IPRARefutationNegationLogic.translatedNegationEquivalent
