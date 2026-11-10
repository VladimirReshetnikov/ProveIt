import DiophantineConsistency.Sign14Positive74Model
import DiophantineConsistency.GenericPolynomialBridgeTransport
import DiophantineConsistency.Sign14Optimized86Bridge

/-! SOURCE-ONLY: transport the 86 polynomial bridge to positiveShift Positive74. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74IPRA
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open SetTheory.PA SetTheory.BusyBeaver.ZFC
open HA FoundationPAHFSyntax FoundationHANoZero FoundationZFCConsistencyNat
  FoundationHADeltaZeroGG HACurrentAssembly2011 ArithmeticCantor
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  CurrentWindowCarry2011.ports

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge
    (positiveShift (Sign14Positive74.expression CurrentWindowCarry2011.ports)) := by
  apply GenericPolynomialBridgeTransport.transfer _ _ ?_ Sign14Optimized86IPRA.polynomialBridge
  intro V _ _
  exact Sign14Positive74Model.zero_exists_iff (V := V) CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign14Positive74IPRA
#print axioms DiophantineConsistency.Sign14Positive74IPRA.polynomialBridge
