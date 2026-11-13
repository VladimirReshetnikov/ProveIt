import DiophantineConsistency.Sign17ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign18DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign18 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign17CurrentExpression.expression Sign18CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign17CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign18DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign17ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign17DirectIPRA
#print axioms DiophantineConsistency.Sign17DirectIPRA.polynomialBridge
