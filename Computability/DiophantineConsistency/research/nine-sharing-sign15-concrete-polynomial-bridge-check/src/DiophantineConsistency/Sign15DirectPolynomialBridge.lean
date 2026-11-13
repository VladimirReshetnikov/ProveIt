import DiophantineConsistency.Sign15ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign16DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign16 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign15DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign15CurrentExpression.expression Sign16CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign15CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign16DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign15ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign15DirectIPRA
#print axioms DiophantineConsistency.Sign15DirectIPRA.polynomialBridge
