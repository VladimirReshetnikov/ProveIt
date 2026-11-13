import DiophantineConsistency.Sign25GenericStandard
import DiophantineConsistency.Sign25DirectPolynomialBridge

/-! SOURCE-ONLY candidate: specialize the generic theorem to sign25. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25GenericStandard
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign25CurrentExpression.expression SharingSeed25Octic.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem standard_current : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign25CurrentExpression.expression 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_bridge Sign25CurrentExpression.expression Sign25DirectIPRA.polynomialBridge
end DiophantineConsistency.Sign25GenericStandard
#print axioms DiophantineConsistency.Sign25GenericStandard.standard_current
