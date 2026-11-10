import DiophantineConsistency.Sign24ExpressionEquivalence
import DiophantineConsistency.GenericPolynomialBridgeTransport

/-! SOURCE-ONLY: specialize model-zero transport before importing the old bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24StagedIPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign24CurrentExpression.expression Sign25CurrentExpression.expression

theorem transfer_from_sign25
    (hb : HAExpressionAssembly.PolynomialBridge Sign25CurrentExpression.expression) :
    HAExpressionAssembly.PolynomialBridge Sign24CurrentExpression.expression := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ hb
  intro V _ _
  exact Sign24ExpressionEquivalence.zero_exists_iff (V := V)
end DiophantineConsistency.Sign24StagedIPRA
#print axioms DiophantineConsistency.Sign24StagedIPRA.transfer_from_sign25
