import DiophantineConsistency.IPRANamedValues51Native
import DiophantineConsistency.AdaptiveDirectQ50
import DiophantineConsistency.AdaptiveDirectQ50Literal

/-! Native endpoint for the 50-variable direct-Q quartic literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRADirectQ50Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 50) := positiveShift
  (AdaptiveDirectQ50Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues51Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRANamedValues51Native.literalNatural, AdaptiveDirectQ50Literal.literal_eq] using
    (AdaptiveDirectQ50.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge50 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues51Native.literalNatural
    sameNoZero IPRANamedValues51Native.bridge51

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveDirectQ50Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge50
end DiophantineConsistency.IPRADirectQ50Native
