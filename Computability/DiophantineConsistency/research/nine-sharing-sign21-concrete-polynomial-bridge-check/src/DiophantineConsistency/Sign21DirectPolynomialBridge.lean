import DiophantineConsistency.Sign21ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign22DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign22 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign21CurrentExpression.expression Sign22CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign21CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign22DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign21ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign21DirectIPRA
#print axioms DiophantineConsistency.Sign21DirectIPRA.polynomialBridge
