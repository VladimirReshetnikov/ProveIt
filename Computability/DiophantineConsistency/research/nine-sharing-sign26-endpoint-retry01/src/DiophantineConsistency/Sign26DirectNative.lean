import DiophantineConsistency.Sign26DirectPolynomialBridge
import DiophantineConsistency.IPRAExpressionNative

/-! SOURCE-ONLY UNCOMPILED native iPRA endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign26CurrentExpression.expression SharingSeed26Sextic.seed
  CurrentWindowCarry2011.ports IPRAExpressionNative.nativeNoZero

abbrev expression := Sign26CurrentExpression.expression

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ polynomialBridge
end DiophantineConsistency.Sign26DirectIPRA
#print axioms DiophantineConsistency.Sign26DirectIPRA.native_equivalence
