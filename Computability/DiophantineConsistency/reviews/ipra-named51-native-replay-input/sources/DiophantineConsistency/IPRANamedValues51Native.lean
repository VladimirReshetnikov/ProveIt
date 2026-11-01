import DiophantineConsistency.IPRANamedValues42Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveNamedValues51

/-! Native endpoint for the fixed-port fifty-one-variable named-value literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANamedValues51Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 51) := positiveShift
  (AdaptiveNamedValues51.literal CurrentWindowCarry2011.ports)

theorem sameNoZero51 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues42Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRANamedValues42Native.literalNatural] using
    (AdaptiveNamedValues51.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge51 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues42Native.literalNatural
    sameNoZero51 IPRANamedValues42Native.bridge42

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveNamedValues51.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge51

end DiophantineConsistency.IPRANamedValues51Native
