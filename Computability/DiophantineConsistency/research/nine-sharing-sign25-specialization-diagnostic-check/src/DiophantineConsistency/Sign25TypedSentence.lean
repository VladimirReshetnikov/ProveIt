import DiophantineConsistency.Sign25GenericStandard
import DiophantineConsistency.Sign25CurrentExpressionDef

/-! SOURCE-ONLY candidate: type the concrete sentence before importing the bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25TypedSentence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage

def sentence : Sentenceᵢ language :=
  IPRAExpressionNative.nativeNoZero Sign25CurrentExpression.expression

theorem sentence_def : sentence =
    IPRAExpressionNative.nativeNoZero Sign25CurrentExpression.expression := rfl
end DiophantineConsistency.Sign25TypedSentence
#print axioms DiophantineConsistency.Sign25TypedSentence.sentence_def
