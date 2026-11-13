import DiophantineConsistency.Sign26DirectPolynomialBridge

/-! SOURCE-ONLY: name the expression and its bridge before native specialization. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign26DirectIPRA
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix
  Sign26CurrentExpression.expression SharingSeed26Sextic.seed CurrentWindowCarry2011.ports

def expression : Expr (Fin 26) := Sign26CurrentExpression.expression

theorem expression_bridge : HAExpressionAssembly.PolynomialBridge expression := polynomialBridge
end DiophantineConsistency.Sign26DirectIPRA
#print axioms DiophantineConsistency.Sign26DirectIPRA.expression_bridge
