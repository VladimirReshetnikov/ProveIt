import DiophantineConsistency.Sign25TypedStandard

/-! SOURCE-ONLY candidate: expose the original direct expression sentence. -/
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

theorem standard_current : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign25CurrentExpression.expression 🡘
      ∼mappedNativeRefutation embedding := by
  rw [← sentence_def]
  exact standard_typed
end DiophantineConsistency.Sign25TypedSentence
#print axioms DiophantineConsistency.Sign25TypedSentence.standard_current
