import DiophantineConsistency.SharingSeed18Shared06

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed18Degree94
def row07 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((shared34 p) * (Expr.var 18))) - (Expr.constant (1 : ℤ)))
end DiophantineConsistency.SharingSeed18Degree94
