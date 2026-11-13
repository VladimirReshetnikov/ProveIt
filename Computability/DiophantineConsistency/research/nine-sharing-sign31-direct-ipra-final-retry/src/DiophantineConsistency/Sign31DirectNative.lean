import DiophantineConsistency.Sign31DirectPolynomialBridge
import DiophantineConsistency.IPRAExpressionNative

/-! UNCOMPILED native iPRA endpoint. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PRALanguage IPRANativeTheory
  IPRAFoundationZFCMappedNegation FoundationZFCConsistencyNat

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero expression 🡘 ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge _ polynomialBridge
end DiophantineConsistency.Sign31DirectIPRA
#print axioms DiophantineConsistency.Sign31DirectIPRA.native_equivalence
