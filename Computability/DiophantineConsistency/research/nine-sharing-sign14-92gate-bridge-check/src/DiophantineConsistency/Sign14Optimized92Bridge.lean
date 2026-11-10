import DiophantineConsistency.Sign14Optimized92Model
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign14Optimized93Bridge

/-! SOURCE-ONLY: transfer the current-port polynomial bridge. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Optimized92IPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011

attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign14Optimized93Expression.expression CurrentWindowCarry2011.ports

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge
    (Sign14Optimized92Expression.expression CurrentWindowCarry2011.ports) := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign14Optimized93IPRA.polynomialBridge
  intro V _ _
  simpa only [Sign14Optimized93Expression.expression] using
    (Sign14Optimized92Model.zero_exists_iff (V := V) CurrentWindowCarry2011.ports)
end DiophantineConsistency.Sign14Optimized92IPRA
#print axioms DiophantineConsistency.Sign14Optimized92IPRA.polynomialBridge
