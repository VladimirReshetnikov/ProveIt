import DiophantineConsistency.SharingSeed18Shared06

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed18Degree94
def row02 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((((Expr.var 15) * (Expr.var 15)) - ((shared25 p) * ((shared25 p) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))
end DiophantineConsistency.SharingSeed18Degree94
