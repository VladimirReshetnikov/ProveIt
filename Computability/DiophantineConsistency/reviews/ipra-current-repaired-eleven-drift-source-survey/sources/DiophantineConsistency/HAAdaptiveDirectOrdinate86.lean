import DiophantineConsistency.HAExpressionAssembly
import DiophantineConsistency.AdaptiveDirectOrdinate86Machine

/-! Exact 86-gate HA endpoint. Provider provenance is established separately. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.HAAdaptiveDirectOrdinate86
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open HA HAExpressionAssembly AdaptiveEquationSyntax2011 FoundationHADeltaZeroGG
attribute [local irreducible] AdaptiveDirectOrdinate86Literal.naturalExpression86

theorem polynomialBridge :
    PolynomialBridge AdaptiveDirectOrdinate86Literal.naturalExpression86 := by
  intro V _ _
  rw [classicalNoZero_iff]
  simpa only [InternalZero, not_exists, ne_eq] using
    (AdaptiveDirectOrdinate86Machine.no_zero_iff_no_run_halt (V := V))

theorem ha_equivalence :
    ProofEquiv
      (ArithmeticExpression.noZeroSentence AdaptiveDirectOrdinate86Literal.naturalExpression86)
      FoundationHAConsistencyNormalization.ordinaryConsistency :=
  HAExpressionAssembly.ha_equivalence _ polynomialBridge
end DiophantineConsistency.HAAdaptiveDirectOrdinate86
