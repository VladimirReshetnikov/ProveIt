import DiophantineConsistency.Sign19ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign20DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign20 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign19DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign19CurrentExpression.expression Sign20CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign19CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign20DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign19ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign19DirectIPRA
#print axioms DiophantineConsistency.Sign19DirectIPRA.polynomialBridge
