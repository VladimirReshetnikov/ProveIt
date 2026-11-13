import DiophantineConsistency.Sign25AssertionStandard

/-! SOURCE-ONLY candidate: expose the original assertion using its equality. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25TypedAssertion
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign25CurrentExpression.expression SharingSeed25Octic.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero assertion

theorem standard_current : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign25CurrentExpression.expression 🡘
      ∼mappedNativeRefutation embedding := by
  rw [← assertion_def]
  exact standard_assertion
end DiophantineConsistency.Sign25TypedAssertion
#print axioms DiophantineConsistency.Sign25TypedAssertion.standard_current
