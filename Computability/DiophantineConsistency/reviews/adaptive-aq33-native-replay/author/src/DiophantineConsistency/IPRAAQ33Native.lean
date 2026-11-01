import DiophantineConsistency.IPRAAQ34Native
import DiophantineConsistency.AdaptiveAQ33

/-! Native endpoint for the fixed-port thirty-three-variable degree-six literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ33Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 33) := positiveShift
  (AdaptiveAQ33Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ34Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRAAQ34Native.literalNatural] using
    (AdaptiveAQ33.current_no_zero_iff (V := V))

theorem bridge33 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ34Native.literalNatural
    sameNoZero IPRAAQ34Native.bridge34

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ33Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge33
end DiophantineConsistency.IPRAAQ33Native
