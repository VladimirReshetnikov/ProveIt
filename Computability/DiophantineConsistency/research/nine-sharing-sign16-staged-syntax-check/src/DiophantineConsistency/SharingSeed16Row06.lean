import DiophantineConsistency.SharingSeed16Shared07

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def row06 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((((shared33 p) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - (shared36 p)) - (shared33 p))
end DiophantineConsistency.SharingSeed16Degree112
