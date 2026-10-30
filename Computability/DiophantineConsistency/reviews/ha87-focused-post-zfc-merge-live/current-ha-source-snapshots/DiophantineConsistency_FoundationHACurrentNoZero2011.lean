import DiophantineConsistency.FoundationHANoZero
import DiophantineConsistency.CurrentEquationSyntax2011

/-! # The exact maintained sentence and its Foundation source

Both implications below are genuine HA proofs. The shared syntax leaf owns
exactly the original current expression, ports and fully-qualified sentence.
No proof of either no-zero sentence or of consistency is supplied here.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.FoundationHACurrentNoZero2011
open LO LO.FirstOrder
open scoped LO.FirstOrder
open SetTheory.PA HA FoundationPAHFSyntax FoundationHANoZero
open ObjectCurrentEquation2011

attribute [local irreducible] expression naturalExpression

/-- A concrete closed arithmetic source with exactly fourteen quantifiers. -/
def classicalSentence : Sentence ℒₒᵣ := classicalNoZero naturalExpression

/-- Literal compilation, with one positive-domain substitution and all ports. -/
theorem current_syntax : ArithmeticCurrentEquation2011.unsolvabilitySentence =
    ArithmeticExpression.noZeroSentence
      (positiveShift (expressionAt CurrentWindowCarry2011.ports)) := by
  simp only [ArithmeticCurrentEquation2011.unsolvabilitySentence, naturalExpression, expression]

theorem translated_source : sentence classicalSentenceᴺ =
    Formula.closeN 14 (neg (reflectedEquation naturalExpression)) :=
  translated_classicalNoZero naturalExpression

theorem source_to_current : Proves (.imp (sentence classicalSentenceᴺ)
    ArithmeticCurrentEquation2011.unsolvabilitySentence) :=
  source_to_noZero naturalExpression

theorem current_to_source : Proves (.imp
    ArithmeticCurrentEquation2011.unsolvabilitySentence (sentence classicalSentenceᴺ)) :=
  noZero_to_source naturalExpression

theorem current_equivalence : Proves (.and
    (.imp (sentence classicalSentenceᴺ) ArithmeticCurrentEquation2011.unsolvabilitySentence)
    (.imp ArithmeticCurrentEquation2011.unsolvabilitySentence (sentence classicalSentenceᴺ))) :=
  source_to_current.and_intro current_to_source

/-- This transports proof existence only; it does not assert either proof exists. -/
theorem proof_exists_iff : Proves (sentence classicalSentenceᴺ) ↔
    Proves ArithmeticCurrentEquation2011.unsolvabilitySentence :=
  ⟨fun h => source_to_current.mp h, fun h => current_to_source.mp h⟩

end DiophantineConsistency.FoundationHACurrentNoZero2011
