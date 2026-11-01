import DiophantineConsistency.IPRANamedValues42Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveNamedValues49

/-! Native endpoint for the fixed-port forty-nine-variable named-value literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANamedValues49Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 49) := positiveShift
  (AdaptiveNamedValues49.literal CurrentWindowCarry2011.ports)

theorem sameNoZero49 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues42Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRANamedValues42Native.literalNatural] using
    (AdaptiveNamedValues49.current_no_zero_iff (V := V))

theorem bridge49 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues42Native.literalNatural
    sameNoZero49 IPRANamedValues42Native.bridge42

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveNamedValues49.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge49

end DiophantineConsistency.IPRANamedValues49Native
