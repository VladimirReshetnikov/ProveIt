import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.HAExpressionSameZero
import DiophantineConsistency.HAExpressionNoZeroEquiv
import DiophantineConsistency.AdaptiveSquareWitness14

/-! Native endpoint for the fixed-port fourteen-variable square-witness literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASquareWitness14Native
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open AdaptiveEquationSyntax2011

def literalNatural : Expr (Fin 14) := positiveShift
  (AdaptiveSquareWitness14.literal CurrentWindowCarry2011.ports)

theorem sameZero13 : HAExpressionSameZero.SameZero
    AdaptiveDirectOrdinateSquareSums.naturalExpression
    AdaptiveDirectOrdinate86Literal.naturalExpression86 := by
  intro V _ _ v
  exact AdaptiveDirectOrdinateSquareSums.current_zero_iff v

theorem bridge13 : HAExpressionAssembly.PolynomialBridge AdaptiveDirectOrdinateSquareSums.naturalExpression :=
  HAExpressionSameZero.bridge86 AdaptiveDirectOrdinateSquareSums.naturalExpression sameZero13

theorem sameNoZero14 : HAExpressionNoZeroEquiv.SameNoZero literalNatural
    AdaptiveDirectOrdinateSquareSums.naturalExpression := by
  intro V _ _
  simpa only [literalNatural, AdaptiveDirectOrdinateSquareSums.naturalExpression,
    AdaptiveDirectOrdinateSquareSums.expression] using
      (AdaptiveSquareWitness14.shifted_no_zero_iff (V := V) CurrentWindowCarry2011.ports)

theorem bridge14 : HAExpressionAssembly.PolynomialBridge literalNatural :=
  HAExpressionNoZeroEquiv.bridge literalNatural AdaptiveDirectOrdinateSquareSums.naturalExpression sameNoZero14 bridge13

theorem literal_equivalence : nativeTheory ⊢ IPRAExpressionNative.nativeNoZero
    (positiveShift (AdaptiveSquareWitness14.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge literalNatural bridge14

end DiophantineConsistency.IPRASquareWitness14Native
