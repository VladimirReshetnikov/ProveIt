import DiophantineConsistency.IPRANamedValues49Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveNamedValues47

/-! Native endpoint for the fixed-port forty-seven-variable named-value literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANamedValues47Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 47) := positiveShift
  (AdaptiveNamedValues47.literal CurrentWindowCarry2011.ports)

theorem sameNoZero47 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues49Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, AdaptiveNamedValues47.literal, IPRANamedValues49Native.literalNatural] using
    (AdaptiveNamedValues47Model.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge47 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues49Native.literalNatural
    sameNoZero47 IPRANamedValues49Native.bridge49

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveNamedValues47.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge47

end DiophantineConsistency.IPRANamedValues47Native
