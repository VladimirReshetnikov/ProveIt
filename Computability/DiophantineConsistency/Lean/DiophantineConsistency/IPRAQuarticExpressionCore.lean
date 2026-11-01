import DiophantineConsistency.QuarticCompilerCore
/-! Natural split syntax used by the generic quartic compiler. -/
namespace DiophantineConsistency.IPRAQuarticExpressionBridge
def left {m : ℕ} (e : Expr (Fin m)) : NatExpr (Empty ⊕ Fin m) := (e.rename Sum.inr).splitNatural.1
def right {m : ℕ} (e : Expr (Fin m)) : NatExpr (Empty ⊕ Fin m) := (e.rename Sum.inr).splitNatural.2
end DiophantineConsistency.IPRAQuarticExpressionBridge
