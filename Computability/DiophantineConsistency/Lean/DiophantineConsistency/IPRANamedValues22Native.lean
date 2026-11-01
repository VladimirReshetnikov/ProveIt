import DiophantineConsistency.IPRARankWitness17Native
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveNamedValues22

/-! Native endpoint for the fixed-port twenty-two-variable named-value literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRANamedValues22Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 22) := positiveShift
  (AdaptiveNamedValues22.literal CurrentWindowCarry2011.ports)

theorem sameNoZero22 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRARankWitness17Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural, IPRARankWitness17Native.literalNatural] using
    (AdaptiveNamedValues22.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge22 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRARankWitness17Native.literalNatural
    sameNoZero22 IPRARankWitness17Native.bridge17

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveNamedValues22.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge22

end DiophantineConsistency.IPRANamedValues22Native
