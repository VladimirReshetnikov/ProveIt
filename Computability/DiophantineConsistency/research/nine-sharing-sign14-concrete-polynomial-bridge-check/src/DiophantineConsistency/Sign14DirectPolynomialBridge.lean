import DiophantineConsistency.Sign14ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign15DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign15 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign14CurrentExpression.expression Sign15CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign14CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign15DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign14ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign14DirectIPRA
#print axioms DiophantineConsistency.Sign14DirectIPRA.polynomialBridge
