import DiophantineConsistency.SharingSeed16Shared07

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def row04 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((Expr.var 16) - ((((shared18 p) * ((Expr.var 7) + (Expr.constant (1 : ℤ)))) + (shared15 p)) - (shared25 p)))
end DiophantineConsistency.SharingSeed16Degree112
