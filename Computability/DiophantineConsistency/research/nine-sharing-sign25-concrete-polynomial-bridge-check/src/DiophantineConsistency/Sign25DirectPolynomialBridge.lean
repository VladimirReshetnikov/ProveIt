import DiophantineConsistency.Sign25ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign26DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign26 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign25CurrentExpression.expression Sign26CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign25CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign26DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign25ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign25DirectIPRA
#print axioms DiophantineConsistency.Sign25DirectIPRA.polynomialBridge
