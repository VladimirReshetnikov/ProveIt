import DiophantineConsistency.Sign16ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign17DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign17 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign16DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign16CurrentExpression.expression Sign17CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign16CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign17DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign16ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign16DirectIPRA
#print axioms DiophantineConsistency.Sign16DirectIPRA.polynomialBridge
