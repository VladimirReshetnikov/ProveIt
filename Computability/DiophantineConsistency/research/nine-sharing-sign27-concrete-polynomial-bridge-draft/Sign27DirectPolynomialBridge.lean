import DiophantineConsistency.Sign27ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign28DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign28 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign27DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign27CurrentExpression.expression Sign28CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign27CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign28DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign27ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign27DirectIPRA
#print axioms DiophantineConsistency.Sign27DirectIPRA.polynomialBridge
