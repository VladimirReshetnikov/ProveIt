import DiophantineConsistency.Sign20ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign21DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign21 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign20CurrentExpression.expression Sign21CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign20CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign21DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign20ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign20DirectIPRA
#print axioms DiophantineConsistency.Sign20DirectIPRA.polynomialBridge
