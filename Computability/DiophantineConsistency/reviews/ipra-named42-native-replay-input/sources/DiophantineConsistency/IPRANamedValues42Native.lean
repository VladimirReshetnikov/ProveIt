import DiophantineConsistency.IPRANamedValues33Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveNamedValues42

/-! Native endpoint for the fixed-port forty-two-variable named-value literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANamedValues42Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 42) := positiveShift
  (AdaptiveNamedValues42.literal CurrentWindowCarry2011.ports)

theorem sameNoZero42 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues33Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRANamedValues33Native.literalNatural] using
    (AdaptiveNamedValues42.current_no_zero_iff (V := V))

theorem bridge42 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues33Native.literalNatural
    sameNoZero42 IPRANamedValues33Native.bridge33

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveNamedValues42.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge42

end DiophantineConsistency.IPRANamedValues42Native
