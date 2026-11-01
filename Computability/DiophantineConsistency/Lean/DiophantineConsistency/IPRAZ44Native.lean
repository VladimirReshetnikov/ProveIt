import DiophantineConsistency.IPRAZ46Native
import DiophantineConsistency.AdaptiveZ44Model

/-! Native endpoint for the fixed-port positive-transport 44-variable literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAZ44Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011 ArithmeticAdaptiveScaledNorms2011

def literalNatural : Expr (Fin 44) := positiveShift
  (AdaptiveZ44Context.literal CurrentWindowCarry2011.ports)

theorem sameNoZero44 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAZ46Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRAZ46Native.literalNatural, currentPorts_cast] using
    (AdaptiveZ44Model.shifted_no_zero_iff (V := V) currentPorts)

theorem bridge44 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAZ46Native.literalNatural
    sameNoZero44 IPRAZ46Native.bridge46

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveZ44Context.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge44
end DiophantineConsistency.IPRAZ44Native
