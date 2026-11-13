import DiophantineConsistency.Sign25TypedSentence
import DiophantineConsistency.Sign25DirectPolynomialBridge

/-! SOURCE-ONLY candidate: specialize the bridge through a typed sentence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25TypedSentence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign25CurrentExpression.expression SharingSeed25Octic.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero sentence

theorem standard_typed : IPRAStandardTheory.standardTheory ⊢
    sentence 🡘 ∼mappedNativeRefutation embedding := by
  rw [sentence_def]
  exact Sign25GenericStandard.standard_of_bridge Sign25CurrentExpression.expression
    Sign25DirectIPRA.polynomialBridge
end DiophantineConsistency.Sign25TypedSentence
#print axioms DiophantineConsistency.Sign25TypedSentence.standard_typed
