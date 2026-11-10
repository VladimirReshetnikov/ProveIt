import DiophantineConsistency.SharingSeed17Shared06

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed17Degree96
def row06 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((shared34 p) * ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((Expr.var 17) * (Expr.var 17))))) - (Expr.constant (1 : ℤ)))
end DiophantineConsistency.SharingSeed17Degree96
