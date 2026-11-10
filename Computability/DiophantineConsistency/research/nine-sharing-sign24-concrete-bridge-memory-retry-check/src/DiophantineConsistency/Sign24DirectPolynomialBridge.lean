import DiophantineConsistency.Sign24ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign25DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign25 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign24CurrentExpression.expression Sign25CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign24CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign25DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign24ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign24DirectIPRA
#print axioms DiophantineConsistency.Sign24DirectIPRA.polynomialBridge
