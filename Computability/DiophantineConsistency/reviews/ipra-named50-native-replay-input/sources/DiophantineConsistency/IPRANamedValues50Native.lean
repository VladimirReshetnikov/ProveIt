import DiophantineConsistency.IPRANamedValues42Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveNamedValues50

/-! Native endpoint for the fixed-port fifty-variable named-value literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANamedValues50Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 50) := positiveShift
  (AdaptiveNamedValues50.literal CurrentWindowCarry2011.ports)

theorem sameNoZero50 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues42Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRANamedValues42Native.literalNatural] using
    (AdaptiveNamedValues50.current_no_zero_iff (V := V))

theorem bridge50 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues42Native.literalNatural
    sameNoZero50 IPRANamedValues42Native.bridge42

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveNamedValues50.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge50

end DiophantineConsistency.IPRANamedValues50Native
