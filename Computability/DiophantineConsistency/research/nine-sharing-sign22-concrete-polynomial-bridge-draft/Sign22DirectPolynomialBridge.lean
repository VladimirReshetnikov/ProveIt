import DiophantineConsistency.Sign22ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign23DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign23 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign22CurrentExpression.expression Sign23CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign22CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign23DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign22ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign22DirectIPRA
#print axioms DiophantineConsistency.Sign22DirectIPRA.polynomialBridge
