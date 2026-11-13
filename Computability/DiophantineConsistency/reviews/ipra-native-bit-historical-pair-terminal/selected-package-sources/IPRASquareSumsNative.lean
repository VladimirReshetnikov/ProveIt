import DiophantineConsistency.IPRAExpressionNative
import DiophantineConsistency.HAExpressionSameZero
import DiophantineConsistency.AdaptiveDirectOrdinateSquareSumsLiteral

/-! Native endpoint for the fixed-port generated square-sum literal. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.IPRASquareSumsNative
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation

theorem sameZero : HAExpressionSameZero.SameZero
    AdaptiveDirectOrdinateSquareSums.naturalExpression
    AdaptiveDirectOrdinate86Literal.naturalExpression86 := by
  intro V _ _ v
  exact AdaptiveDirectOrdinateSquareSums.current_zero_iff v

theorem bridge : HAExpressionAssembly.PolynomialBridge AdaptiveDirectOrdinateSquareSums.naturalExpression :=
  HAExpressionSameZero.bridge86 AdaptiveDirectOrdinateSquareSums.naturalExpression sameZero

theorem equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero AdaptiveDirectOrdinateSquareSums.naturalExpression 🡘
      ∼mappedNativeRefutation embedding :=
  IPRAExpressionNative.equivalence_of_bridge AdaptiveDirectOrdinateSquareSums.naturalExpression bridge

theorem literal_eq : AdaptiveEquationSyntax2011.positiveShift
    (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports) =
    AdaptiveDirectOrdinateSquareSums.naturalExpression := by
  simp only [AdaptiveDirectOrdinateSquareSumsLiteral.literal_eq_optimized,
    AdaptiveDirectOrdinateSquareSums.naturalExpression, AdaptiveDirectOrdinateSquareSums.expression]

theorem literal_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (AdaptiveEquationSyntax2011.positiveShift
      (AdaptiveDirectOrdinateSquareSumsLiteral.literal CurrentWindowCarry2011.ports)) 🡘
      ∼mappedNativeRefutation embedding := by
  rw [literal_eq]
  exact equivalence


end DiophantineConsistency.IPRASquareSumsNative
