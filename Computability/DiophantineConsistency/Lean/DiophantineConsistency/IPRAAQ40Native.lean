import DiophantineConsistency.IPRANamedValues42Native
import DiophantineConsistency.AdaptiveAQ40

/-! Native endpoint for the fixed-port forty-variable direct a/Q literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ40Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 40) := positiveShift
  (AdaptiveAQ40Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues42Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRANamedValues42Native.literalNatural] using
    (AdaptiveAQ40.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge40 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues42Native.literalNatural
    sameNoZero IPRANamedValues42Native.bridge42

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ40Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge40
end DiophantineConsistency.IPRAAQ40Native
