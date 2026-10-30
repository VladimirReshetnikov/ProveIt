import DiophantineConsistency.AdaptiveFirstRootFactor87Literal
import DiophantineConsistency.ArithmeticExpression
set_option autoImplicit false
namespace DiophantineConsistency.AdaptiveFactor87Sentence
open SetTheory.PA
open AdaptiveFirstRootFactor87Literal

def sourceSentence : Formula := ArithmeticExpression.noZeroSentence AdaptiveEquationSyntax2011.naturalExpression
def reducedSentence : Formula := ArithmeticExpression.noZeroSentence naturalExpression87

theorem source_closed : Formula.Sentence sourceSentence :=
  ArithmeticExpression.sentence_noZeroSentence _
theorem reduced_closed : Formula.Sentence reducedSentence :=
  ArithmeticExpression.sentence_noZeroSentence _

theorem semantic_equivalence {R : Type*} [CommSemiring R] :
    (∀ e : ℕ → R, Formula.Sat (ArithmeticExpression.semiringStructure R) e sourceSentence) ↔
    (∀ e : ℕ → R, Formula.Sat (ArithmeticExpression.semiringStructure R) e reducedSentence) := by
  rw [sourceSentence, reducedSentence, ArithmeticExpression.sat_noZeroSentence,
    ArithmeticExpression.sat_noZeroSentence]
  apply forall_congr'
  intro v
  exact not_congr (current_natural_zero_iff v)
end DiophantineConsistency.AdaptiveFactor87Sentence
