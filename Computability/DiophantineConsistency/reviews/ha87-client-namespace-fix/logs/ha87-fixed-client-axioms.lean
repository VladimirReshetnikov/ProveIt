import DiophantineConsistency.HAExpressionAssembly
import DiophantineConsistency.ArithmeticAdaptiveEquivalenceUnconditional2011
/-! Exact 87-gate HA endpoint. Provider provenance is established separately. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.HAAdaptiveFactor87
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open HA HAExpressionAssembly AdaptiveEquationSyntax2011 FoundationHADeltaZeroGG
attribute [local irreducible] AdaptiveFirstRootFactor87Literal.naturalExpression87

/-- The exact 87-gate expression has the required all-model machine bridge. -/
theorem polynomialBridge :
    PolynomialBridge AdaptiveFirstRootFactor87Literal.naturalExpression87 := by
  intro V _ _
  rw [classicalNoZero_iff]
  simpa only [InternalZero, not_exists, ne_eq] using
    (ArithmeticAdaptiveEquivalenceUnconditional2011.no_zero_iff_no_run_halt (V := V))

/-- Actual HA derivation: the exact 87-gate no-zero sentence is equivalent
to Foundation's ordinary ZFC consistency sentence. -/
theorem ha_equivalence :
    ProofEquiv
      (ArithmeticExpression.noZeroSentence AdaptiveFirstRootFactor87Literal.naturalExpression87)
      FoundationHAConsistencyNormalization.ordinaryConsistency :=
  HAExpressionAssembly.ha_equivalence _ polynomialBridge
end DiophantineConsistency.HAAdaptiveFactor87

#print axioms DiophantineConsistency.HAAdaptiveFactor87.polynomialBridge
#print axioms DiophantineConsistency.HAAdaptiveFactor87.ha_equivalence
