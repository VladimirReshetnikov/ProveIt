import DiophantineConsistency.Sign25DirectPolynomialBridge

/-! SOURCE-ONLY: name the expression and its bridge before native specialization. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign25DirectIPRA
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign25CurrentExpression.expression SharingSeed25Octic.seed CurrentWindowCarry2011.ports

def expression : Expr (Fin 25) := Sign25CurrentExpression.expression

theorem expression_bridge : HAExpressionAssembly.PolynomialBridge expression := polynomialBridge
end DiophantineConsistency.Sign25DirectIPRA
#print axioms DiophantineConsistency.Sign25DirectIPRA.expression_bridge
