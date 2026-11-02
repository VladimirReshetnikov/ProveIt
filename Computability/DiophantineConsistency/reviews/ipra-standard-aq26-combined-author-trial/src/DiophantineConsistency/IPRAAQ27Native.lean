import DiophantineConsistency.IPRAAQ28Native
import DiophantineConsistency.AdaptiveAQ27

/-! Native endpoint for the fixed-port 27-variable degree-eight literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ27Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 27) := positiveShift
  (AdaptiveAQ27Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ28Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural,IPRAAQ28Native.literalNatural] using
    (AdaptiveAQ27.current_no_zero_iff (V := V))

theorem bridge27 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ28Native.literalNatural
    sameNoZero IPRAAQ28Native.bridge28

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ27Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge27
#print axioms sameNoZero
#print axioms bridge27
#print axioms literal_equivalence
end DiophantineConsistency.IPRAAQ27Native
