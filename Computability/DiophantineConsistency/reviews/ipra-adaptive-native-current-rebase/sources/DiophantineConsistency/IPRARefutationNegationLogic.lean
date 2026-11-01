import Foundation.FirstOrder.NegationTranslation.GoedelGentzen

/-! The purely intuitionistic final step for normalizing a refutation negation.
No arithmetic axioms, bounded-decision claim or proof translator are assumed. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRARefutationNegationLogic
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder

variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L}

/-- If the native predicate implies its translation, and the translation
implies the native predicate's double negation, their negations agree. -/
def negationsEquivalent (ordinary translated : Propositionᵢ L)
    (hforward : Λ ⊢! ordinary 🡒 translated)
    (hbackward : Λ ⊢! translated 🡒 ∼∼ordinary) :
    Λ ⊢! ∼translated 🡘 ∼ordinary :=
  Entailment.K_intro (Entailment.contra hforward)
    (Entailment.C_trans Entailment.dni (Entailment.contra hbackward))

/-- The exact Foundation Gödel–Gentzen image of a source negation agrees
with the ordinary negation, conditional on the two displayed implications. -/
def translatedNegationEquivalent (ρ : Proposition L) (ordinary : Propositionᵢ L)
    (hforward : Λ ⊢! ordinary 🡒 ρᴺ)
    (hbackward : Λ ⊢! ρᴺ 🡒 ∼∼ordinary) :
    Λ ⊢! (∼ρ)ᴺ 🡘 ∼ordinary := by
  have hneg := negationsEquivalent ordinary ρᴺ hforward hbackward
  have hsource : Λ ⊢! ∼ρᴺ 🡘 (∼ρ)ᴺ := Derivation.negDoubleNegation ρ
  exact Entailment.K_intro
    (Entailment.C_trans (Entailment.K_right hsource) (Entailment.K_left hneg))
    (Entailment.C_trans (Entailment.K_right hneg) (Entailment.K_left hsource))
end DiophantineConsistency.IPRARefutationNegationLogic
