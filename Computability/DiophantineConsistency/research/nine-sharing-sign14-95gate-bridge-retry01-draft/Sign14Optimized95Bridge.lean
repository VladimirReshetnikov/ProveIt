import DiophantineConsistency.Sign14Optimized95Model
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign14DirectPolynomialBridge

/-! SOURCE-ONLY: transfer the symbolic current-port polynomial bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized95IPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign14CurrentExpression.expression CurrentWindowCarry2011.ports

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge
    (Sign14Optimized95Expression.expression CurrentWindowCarry2011.ports) := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign14DirectIPRA.polynomialBridge
  intro V _ _
  simpa only [Sign14CurrentExpression.expression] using
    (Sign14Optimized95Model.zero_exists_iff (V := V) CurrentWindowCarry2011.ports)
end DiophantineConsistency.Sign14Optimized95IPRA
#print axioms DiophantineConsistency.Sign14Optimized95IPRA.polynomialBridge
