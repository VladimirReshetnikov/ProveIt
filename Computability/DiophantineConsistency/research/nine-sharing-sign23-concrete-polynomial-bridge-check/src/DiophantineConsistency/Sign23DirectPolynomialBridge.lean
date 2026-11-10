import DiophantineConsistency.Sign23ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign24DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign24 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign23CurrentExpression.expression Sign24CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign23CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign24DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign23ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign23DirectIPRA
#print axioms DiophantineConsistency.Sign23DirectIPRA.polynomialBridge
