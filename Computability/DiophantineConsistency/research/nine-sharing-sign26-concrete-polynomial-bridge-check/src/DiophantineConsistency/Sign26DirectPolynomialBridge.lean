import DiophantineConsistency.Sign26ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign27DirectPolynomialBridge

/-! SOURCE-ONLY: transport the checked sign27 bridge through model-zero equivalence. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26DirectIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign26CurrentExpression.expression Sign27CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign26CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign27DirectIPRA.polynomialBridge
  intro V _ _
  exact Sign26ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign26DirectIPRA
#print axioms DiophantineConsistency.Sign26DirectIPRA.polynomialBridge
