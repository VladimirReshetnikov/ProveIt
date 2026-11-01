import DiophantineConsistency.IPRAAQ33Native
import DiophantineConsistency.AdaptiveAQ32

/-! Native endpoint for the fixed-port thirty-two-variable degree-six literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ32Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 32) := positiveShift
  (AdaptiveAQ32Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ33Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRAAQ33Native.literalNatural] using
    (AdaptiveAQ32.current_no_zero_iff (V := V))

theorem bridge32 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ33Native.literalNatural
    sameNoZero IPRAAQ33Native.bridge33

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ32Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge32
end DiophantineConsistency.IPRAAQ32Native
