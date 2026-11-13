import DiophantineConsistency.SharingSeed15Shared07

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def row04 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((shared39 p) * ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((shared33 p) * (shared33 p))))) - (Expr.constant (1 : ℤ)))
end DiophantineConsistency.SharingSeed15Degree124
