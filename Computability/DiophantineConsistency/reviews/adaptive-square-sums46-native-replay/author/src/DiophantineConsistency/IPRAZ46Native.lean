import DiophantineConsistency.IPRANamedValues47Native
import DiophantineConsistency.AdaptiveZ46Model

/-! Native endpoint for the fixed-port oriented-root 46-variable literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAZ46Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 46) := positiveShift
  (AdaptiveZ46Context.literal CurrentWindowCarry2011.ports)

theorem sameNoZero46 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRANamedValues47Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRANamedValues47Native.literalNatural] using
    (AdaptiveZ46Model.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge46 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRANamedValues47Native.literalNatural
    sameNoZero46 IPRANamedValues47Native.bridge47

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveZ46Context.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge46
end DiophantineConsistency.IPRAZ46Native
