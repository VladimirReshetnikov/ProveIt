import DiophantineConsistency.IPRAAQ27Native
import DiophantineConsistency.AdaptiveAQ26

/-! Native endpoint for the fixed-port 26-variable degree-eight literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ26Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 26) := positiveShift
  (AdaptiveAQ26Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ27Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural,IPRAAQ27Native.literalNatural] using
    (AdaptiveAQ26.current_no_zero_iff (V := V))

theorem bridge26 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ27Native.literalNatural
    sameNoZero IPRAAQ27Native.bridge27

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ26Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge26
#print axioms sameNoZero
#print axioms bridge26
#print axioms literal_equivalence
end DiophantineConsistency.IPRAAQ26Native
