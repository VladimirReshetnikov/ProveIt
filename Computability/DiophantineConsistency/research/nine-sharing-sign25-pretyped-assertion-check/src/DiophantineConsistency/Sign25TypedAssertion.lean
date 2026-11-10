import DiophantineConsistency.Sign25GenericStandard
import DiophantineConsistency.Sign25CurrentExpressionDef

/-! SOURCE-ONLY candidate: type the full assertion before importing the bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25TypedAssertion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

def assertion : Sentenceᵢ language :=
  IPRAExpressionNative.nativeNoZero Sign25CurrentExpression.expression 🡘
    ∼mappedNativeRefutation embedding

theorem assertion_def : assertion =
    (IPRAExpressionNative.nativeNoZero Sign25CurrentExpression.expression 🡘
      ∼mappedNativeRefutation embedding) := rfl
end DiophantineConsistency.Sign25TypedAssertion
#print axioms DiophantineConsistency.Sign25TypedAssertion.assertion_def
