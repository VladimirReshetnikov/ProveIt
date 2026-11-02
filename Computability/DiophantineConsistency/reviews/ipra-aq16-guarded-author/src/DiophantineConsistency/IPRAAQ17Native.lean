import DiophantineConsistency.IPRAAQ22Native
import DiophantineConsistency.AdaptiveAQ17

/-! Native endpoint for the fixed-port 22-variable degree-ten literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ17Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 17) := positiveShift
  (AdaptiveAQ17Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ22Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural,IPRAAQ22Native.literalNatural] using
    (AdaptiveAQ17.current_no_zero_iff (V := V))

theorem bridge17 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ22Native.literalNatural
    sameNoZero IPRAAQ22Native.bridge22

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ17Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge17
#print axioms sameNoZero
#print axioms bridge17
#print axioms literal_equivalence
end DiophantineConsistency.IPRAAQ17Native
