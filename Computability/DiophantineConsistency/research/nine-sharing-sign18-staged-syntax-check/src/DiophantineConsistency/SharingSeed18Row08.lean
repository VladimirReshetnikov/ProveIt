import DiophantineConsistency.SharingSeed18Shared06

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed18Degree94
def row08 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((((shared31 p) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - (shared34 p)) - (shared31 p))
end DiophantineConsistency.SharingSeed18Degree94
