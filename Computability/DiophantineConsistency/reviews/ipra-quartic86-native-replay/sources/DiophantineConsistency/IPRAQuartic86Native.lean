import DiophantineConsistency.IPRAQuarticNativeBridge
import DiophantineConsistency.HAAdaptiveDirectOrdinate86
/-! No-premise native transfer for the mechanically generated tree quartic.
This compiler uses one wire per syntax-tree node; its size is separate from
the compact 51-variable displayed quartic. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAQuartic86Native
open LO LO.FirstOrder LO.Entailment
open scoped LO.FirstOrder
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011 IPRAQuarticPositiveBridge

theorem equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift
      (rawQuartic AdaptiveDirectOrdinate86Literal.naturalExpression86)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAQuarticNativeBridge.native_equivalence _ HAAdaptiveDirectOrdinate86.polynomialBridge
#print axioms equivalence
end DiophantineConsistency.IPRAQuartic86Native
