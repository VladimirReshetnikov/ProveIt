import DiophantineConsistency.Sign31AbstractExpressionEval

/-! UNCOMPILED diagnostic: closed current-port expression definition only. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign31CurrentExpression
open AdaptiveEquationSyntax2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort CurrentMasks2011.radix

def expression : Expr (Fin 31) := Sign31AbstractExpression.expression CurrentWindowCarry2011.ports
end DiophantineConsistency.Sign31CurrentExpression
