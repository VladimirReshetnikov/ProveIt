import DiophantineConsistency.Sign25TypedAssertion
import DiophantineConsistency.Sign25DirectPolynomialBridge

/-! SOURCE-ONLY candidate: specialize through the pretyped full assertion. -/
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

theorem standard_assertion : IPRAStandardTheory.standardTheory ⊢ assertion :=
  Sign25GenericStandard.standard_of_bridge_eq Sign25CurrentExpression.expression
    Sign25DirectIPRA.polynomialBridge assertion assertion_def
end DiophantineConsistency.Sign25TypedAssertion
#print axioms DiophantineConsistency.Sign25TypedAssertion.standard_assertion
