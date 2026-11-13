import DiophantineConsistency.Sign31CurrentExpressionSource
import DiophantineConsistency.HACurrentEquation2011

/-! UNCOMPILED direct sign31 expression-to-source polynomial bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing

abbrev expression := Sign31CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge expression := by
  intro V _ _
  have currentBridge : HAExpressionAssembly.PolynomialBridge ObjectCurrentEquation2011.naturalExpression :=
    fun W _ _ => HACurrentEquation2011.polynomialBridge W
  have hB := currentBridge V
  rw [HAExpressionAssembly.classicalNoZero_iff] at hB ⊢
  rw [← hB]
  simpa only [InternalZero, ObjectCurrentEquation2011.InternalZero, not_exists, ne_eq] using not_congr (Sign31CurrentExpression.zero_iff_current (V := V))
end DiophantineConsistency.Sign31DirectIPRA
#print axioms DiophantineConsistency.Sign31DirectIPRA.polynomialBridge
