import DiophantineConsistency.IPRAAQ26Native
import DiophantineConsistency.AdaptiveAQ22

/-! Native endpoint for the fixed-port 22-variable degree-ten literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ22Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 22) := positiveShift
  (AdaptiveAQ22Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ26Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural,IPRAAQ26Native.literalNatural] using
    (AdaptiveAQ22.current_no_zero_iff (V := V))

theorem bridge22 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ26Native.literalNatural
    sameNoZero IPRAAQ26Native.bridge26

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ22Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge22
#print axioms sameNoZero
#print axioms bridge22
#print axioms literal_equivalence
end DiophantineConsistency.IPRAAQ22Native
