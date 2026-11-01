import DiophantineConsistency.IPRAAQ31Native
import DiophantineConsistency.AdaptiveAQ30

/-! Native endpoint for the fixed-port thirty-variable degree-eight literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRAAQ30Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 30) := positiveShift
  (AdaptiveAQ30Literal.literal CurrentWindowCarry2011.ports)

theorem sameNoZero : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    (positiveShift (AdaptiveAQ31Literal.literal CurrentWindowCarry2011.ports)) := by
  intro V _ _
  simpa only [literalNatural] using (AdaptiveAQ30.current_no_zero_iff (V := V))

theorem bridge30 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural _ sameNoZero
    (IPRAAQ31ConditionalBridge.bridge31_of_machineOrients IPRAAQ31Native.machineOrients)

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveAQ30Literal.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge30
#print axioms sameNoZero
#print axioms bridge30
#print axioms literal_equivalence
end DiophantineConsistency.IPRAAQ30Native
