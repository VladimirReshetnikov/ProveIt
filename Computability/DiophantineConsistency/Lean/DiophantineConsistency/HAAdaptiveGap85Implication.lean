import DiophantineConsistency.HAExpressionImplication
import DiophantineConsistency.AdaptiveGap85Machine

/-! One-sided 85-gate HA endpoint. A coherent provider replay is required. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.HAAdaptiveGap85Implication
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open HA HAExpressionAssembly HAExpressionImplication AdaptiveEquationSyntax2011
attribute [local irreducible] AdaptiveGap85Machine.naturalExpression85

theorem polynomialImplication :
    PolynomialImplication AdaptiveGap85Machine.naturalExpression85 := by
  intro V _ _
  rw [classicalNoZero_iff]
  intro hz
  have hn : ∀ v : Fin 13 → V, ¬InternalZero AdaptiveGap85Machine.naturalExpression85 v := by
    simpa only [InternalZero,ne_eq] using hz
  have h := AdaptiveGap85Machine.no_zero_implies_no_run_halt hn
  simpa only [not_exists,ne_eq] using h

theorem ha_implication :
    Proves (.imp (ArithmeticExpression.noZeroSentence AdaptiveGap85Machine.naturalExpression85)
      FoundationHAConsistencyNormalization.ordinaryConsistency) :=
  HAExpressionImplication.ha_implication _ polynomialImplication
end DiophantineConsistency.HAAdaptiveGap85Implication
