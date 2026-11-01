import DiophantineConsistency.IPRARefutationNegationLogic

/-! Conditional normalization under an arbitrary intuitionistic theory. -/
set_option autoImplicit false
namespace DiophantineConsistency.IPRARefutationNegationTheory
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder

variable {L : Language} [L.DecidableEq] {Λ : Hilbertᵢ L} {T : Theoryᵢ L Λ}

/-- The two comparisons may be proved from the same intuitionistic theory. -/
def theoryNegationsEquivalent (ordinary translated : Sentenceᵢ L)
    (hforward : T ⊢! ordinary 🡒 translated)
    (hbackward : T ⊢! translated 🡒 ∼∼ordinary) :
    T ⊢! ∼translated 🡘 ∼ordinary :=
  Entailment.K_intro (Entailment.contra hforward)
    (Entailment.C_trans Entailment.dni (Entailment.contra hbackward))

/-- Exact Foundation GG negation, conditional on two proofs in the same
intuitionistic theory. No arithmetic or decidability premise is asserted. -/
def theoryTranslatedNegationEquivalent (ρ : Sentence L) (ordinary : Sentenceᵢ L)
    (hforward : T ⊢! ordinary 🡒 ρᴺ)
    (hbackward : T ⊢! ρᴺ 🡒 ∼∼ordinary) :
    T ⊢! (∼ρ)ᴺ 🡘 ∼ordinary := by
  have hneg := theoryNegationsEquivalent ordinary ρᴺ hforward hbackward
  have hsource : T ⊢! ∼ρᴺ 🡘 (∼ρ)ᴺ := by
    apply Theoryᵢ.ofHilbert
    have h := Derivation.negDoubleNegation (Λ := Λ) (Rewriting.emb ρ)
    simpa only [Semiformula.emb_doubleNegation, LogicalConnective.HomClass.map_neg,
      LogicalConnective.HomClass.map_iff] using h
  exact Entailment.K_intro
    (Entailment.C_trans (Entailment.K_right hsource) (Entailment.K_left hneg))
    (Entailment.C_trans (Entailment.K_right hneg) (Entailment.K_left hsource))
end DiophantineConsistency.IPRARefutationNegationTheory
