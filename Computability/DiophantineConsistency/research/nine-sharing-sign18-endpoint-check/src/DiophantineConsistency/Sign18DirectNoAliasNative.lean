import DiophantineConsistency.Sign18DirectPolynomialBridge
import DiophantineConsistency.IPRAExpressionNative

/-! SOURCE-ONLY candidate: native endpoint for the existing expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign18DirectNoAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign18CurrentExpression.expression SharingSeed18Degree94.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign18CurrentExpression.expression 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge Sign18CurrentExpression.expression
    Sign18DirectIPRA.polynomialBridge
end DiophantineConsistency.Sign18DirectNoAlias
#print axioms DiophantineConsistency.Sign18DirectNoAlias.native_equivalence
