import DiophantineConsistency.Sign20DirectPolynomialBridge
import DiophantineConsistency.IPRAExpressionNative

/-! SOURCE-ONLY candidate: native endpoint for the existing expression. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20DirectNoAlias
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign20CurrentExpression.expression SharingSeed20Degree20.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero Sign20CurrentExpression.expression 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge Sign20CurrentExpression.expression
    Sign20DirectIPRA.polynomialBridge
end DiophantineConsistency.Sign20DirectNoAlias
#print axioms DiophantineConsistency.Sign20DirectNoAlias.native_equivalence
