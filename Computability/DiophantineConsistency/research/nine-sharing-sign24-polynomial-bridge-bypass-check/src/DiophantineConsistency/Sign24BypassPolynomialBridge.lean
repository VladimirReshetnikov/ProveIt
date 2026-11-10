import DiophantineConsistency.Sign24ExpressionEquivalence
import DiophantineConsistency.Sign25ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign26DirectPolynomialBridge

/-! SOURCE-ONLY: bypass the concrete sign25 bridge through two zero iff lemmas. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24BypassIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign24CurrentExpression.expression Sign25CurrentExpression.expression
  Sign26CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign24CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign26DirectIPRA.polynomialBridge
  intro V _ _
  exact (Sign24ExpressionEquivalence.zero_exists_iff (V := V)).trans
    (Sign25ExpressionEquivalence.zero_exists_iff (V := V))
end DiophantineConsistency.Sign24BypassIPRA
#print axioms DiophantineConsistency.Sign24BypassIPRA.polynomialBridge
