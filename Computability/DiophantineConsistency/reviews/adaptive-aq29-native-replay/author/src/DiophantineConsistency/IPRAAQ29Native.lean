import DiophantineConsistency.IPRAAQ30Native
import DiophantineConsistency.AdaptiveAQ29

/-! Native endpoint for the fixed-port twenty-nine-variable degree-eight literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ29Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 29) := positiveShift
  (AdaptiveAQ29Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    IPRAAQ30Native.literalNatural := by
  intro V _ _
  simpa only [literalNatural,IPRAAQ30Native.literalNatural] using
    (AdaptiveAQ29.current_no_zero_iff (V := V))

theorem bridge29 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural IPRAAQ30Native.literalNatural
    sameNoZero IPRAAQ30Native.bridge30

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ29Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge29
#print axioms sameNoZero
#print axioms bridge29
#print axioms literal_equivalence
end DiophantineConsistency.IPRAAQ29Native
