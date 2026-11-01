import DiophantineConsistency.IPRAAQ40Native
import DiophantineConsistency.AdaptiveAQ36

/-! Native endpoint for the fixed-port thirty-six-variable literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ36Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 36) := positiveShift
  (AdaptiveAQ36Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ40Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRAAQ40Native.literalNatural] using
    (AdaptiveAQ36.current_no_zero_iff (V := V))

theorem bridge36 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ40Native.literalNatural
    sameNoZero IPRAAQ40Native.bridge40

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ36Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge36
end DiophantineConsistency.IPRAAQ36Native
