import DiophantineConsistency.IPRAAQ35Native
import DiophantineConsistency.AdaptiveAQ34

/-! Native endpoint for the fixed-port thirty-four-variable literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ34Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 34) := positiveShift
  (AdaptiveAQ34Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ35Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRAAQ35Native.literalNatural] using
    (AdaptiveAQ34.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge34 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ35Native.literalNatural
    sameNoZero IPRAAQ35Native.bridge35

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ34Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge34
end DiophantineConsistency.IPRAAQ34Native
