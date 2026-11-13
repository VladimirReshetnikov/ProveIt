import DiophantineConsistency.Sign24BridgeConditional
import DiophantineConsistency.Sign25DirectPolynomialBridge

/-! SOURCE-ONLY: instantiate the previously specialized transport. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24StagedIPRA
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign24CurrentExpression.expression Sign25CurrentExpression.expression

theorem polynomialBridge : HAExpressionAssembly.PolynomialBridge Sign24CurrentExpression.expression :=
  transfer_from_sign25 Sign25DirectIPRA.polynomialBridge
end DiophantineConsistency.Sign24StagedIPRA
#print axioms DiophantineConsistency.Sign24StagedIPRA.polynomialBridge
