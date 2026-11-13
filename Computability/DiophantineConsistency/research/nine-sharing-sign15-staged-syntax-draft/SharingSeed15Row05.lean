import DiophantineConsistency.SharingSeed15Shared07

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def row05 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((((shared36 p) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - (shared39 p)) - (shared36 p))
end DiophantineConsistency.SharingSeed15Degree124
