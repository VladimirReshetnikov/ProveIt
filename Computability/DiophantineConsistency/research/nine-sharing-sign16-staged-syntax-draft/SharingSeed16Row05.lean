import DiophantineConsistency.SharingSeed16Shared07

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def row05 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((shared36 p) * ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((shared20 p) * (shared20 p))))) - (Expr.constant (1 : ℤ)))
end DiophantineConsistency.SharingSeed16Degree112
