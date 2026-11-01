import DiophantineConsistency.IPRANamedValues22Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveNamedValues26

/-! Native endpoint for the fixed-port twenty-six-variable named-value literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANamedValues26Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 26) := positiveShift
  (AdaptiveNamedValues26.literal CurrentWindowCarry2011.ports)

theorem sameNoZero26 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues22Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRANamedValues22Native.literalNatural] using
    (AdaptiveNamedValues26.current_no_zero_iff (V := V))

theorem bridge26 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues22Native.literalNatural
    sameNoZero26 IPRANamedValues22Native.bridge22

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveNamedValues26.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge26

end DiophantineConsistency.IPRANamedValues26Native
