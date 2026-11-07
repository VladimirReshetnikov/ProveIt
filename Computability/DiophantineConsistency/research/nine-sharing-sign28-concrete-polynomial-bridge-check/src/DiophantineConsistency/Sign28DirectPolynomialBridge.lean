import DiophantineConsistency.Sign28ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign31DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign31 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign28DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign28CurrentExpression.expression Sign31CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign28CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign31DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign28ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign28DirectIPRA
#print axioms DiophantineConsistency.Sign28DirectIPRA.polynomialBridge
