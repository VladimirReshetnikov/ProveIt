import DiophantineConsistency.IPRAAQ36Native
import DiophantineConsistency.AdaptiveAQ35

/-! Native endpoint for the fixed-port thirty-five-variable literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ35Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 35) := positiveShift
  (AdaptiveAQ35Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ36Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRAAQ36Native.literalNatural] using
    (AdaptiveAQ35.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge35 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ36Native.literalNatural
    sameNoZero IPRAAQ36Native.bridge36

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ35Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge35
end DiophantineConsistency.IPRAAQ35Native
