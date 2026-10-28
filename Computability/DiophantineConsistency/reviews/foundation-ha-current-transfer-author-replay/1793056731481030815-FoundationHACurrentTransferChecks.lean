import DiophantineConsistency.FoundationHACurrentTransfer

set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.FoundationHACurrentTransferChecks
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax FoundationHACurrentNoZero2011
open FoundationHACurrentTransfer

/-- The exact maintained FQName occurs, with no stability premise for χ. -/
theorem actual_current_forward {χ : ArithmeticSentence}
    (h : Peano ⊢ classicalSentence 🡘 χ) :
    Proves (.imp ArithmeticCurrentEquation2011.unsolvabilitySentence (sentence χᴺ)) :=
  (current_iff_translated h).and_left

theorem actual_current_backward {χ : ArithmeticSentence}
    (h : Peano ⊢ classicalSentence 🡘 χ) :
    Proves (.imp (sentence χᴺ) ArithmeticCurrentEquation2011.unsolvabilitySentence) :=
  (current_iff_translated h).and_right

/-- Negation is literal, with an arbitrary source predicate still explicit. -/
theorem negative_target {ρ : ArithmeticSentence}
    (h : Peano ⊢ classicalSentence 🡘 ∼ρ) : Proves (.and
      (.imp ArithmeticCurrentEquation2011.unsolvabilitySentence (neg (sentence ρᴺ)))
      (.imp (neg (sentence ρᴺ)) ArithmeticCurrentEquation2011.unsolvabilitySentence)) :=
  current_iff_neg_translated h

/-- Implication elimination does not silently discard open assumptions. -/
theorem retained_context (G : List Formula) (φ ψ : Proposition ℒₒᵣ)
    (h : Relative Formula.Ax_s G (formula (φ 🡒 ψ)ᴺ)) :
    Relative Formula.Ax_s G (.imp (formula φᴺ) (formula ψᴺ)) :=
  translated_imp_elim φ ψ h

theorem negative_bottom : Proves (.and
    (.imp (neg (sentence (⊥ : ArithmeticSentence)ᴺ)) (sentence (∼(⊥ : ArithmeticSentence))ᴺ))
    (.imp (sentence (∼(⊥ : ArithmeticSentence))ᴺ) (neg (sentence (⊥ : ArithmeticSentence)ᴺ)))) :=
  translated_neg ⊥

#print axioms translated_imp_elim
#print axioms sentence_imp_elim
#print axioms current_iff_translated
#print axioms translated_neg
#print axioms current_iff_neg_translated
#print axioms actual_current_forward
#print axioms actual_current_backward
#print axioms negative_target
#print axioms retained_context
#print axioms negative_bottom
end DiophantineConsistency.FoundationHACurrentTransferChecks
