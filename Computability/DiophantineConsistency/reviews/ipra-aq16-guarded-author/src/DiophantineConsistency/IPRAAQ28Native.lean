import DiophantineConsistency.IPRAAQ29Native
import DiophantineConsistency.AdaptiveAQ28

/-! Native endpoint for the fixed-port 28-variable degree-eight literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ28Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 28) := positiveShift
  (AdaptiveAQ28Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ29Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural,IPRAAQ29Native.literalNatural] using
    (AdaptiveAQ28.current_no_zero_iff (V := V))

theorem bridge28 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ29Native.literalNatural
    sameNoZero IPRAAQ29Native.bridge29

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ28Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge28
#print axioms sameNoZero
#print axioms bridge28
#print axioms literal_equivalence
end DiophantineConsistency.IPRAAQ28Native
