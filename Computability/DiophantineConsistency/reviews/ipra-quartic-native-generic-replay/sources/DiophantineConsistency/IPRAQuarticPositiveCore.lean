import DiophantineConsistency.IPRAQuarticExpressionCore
import DiophantineConsistency.QuarticSyntaxCore
import DiophantineConsistency.PositiveOffsetCore
/-! Raw quartic syntax with each variable offset by one. -/
namespace DiophantineConsistency.IPRAQuarticPositiveBridge
open QuarticCompiler IPRAQuarticExpressionBridge PositiveOffsetArithmetic
def rawQuartic {m : ℕ} (e : Expr (Fin m)) : Expr (Fin (witnessCount (left e) (right e) + 1)) :=
  decrement (QuarticSyntax.expression (left e) (right e))
end DiophantineConsistency.IPRAQuarticPositiveBridge
