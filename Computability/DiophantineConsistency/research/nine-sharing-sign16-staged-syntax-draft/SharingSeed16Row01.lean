import DiophantineConsistency.SharingSeed16Shared07

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def row01 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((Expr.var 15) - (((((shared19 p) * ((Expr.var 10) + (Expr.constant (1 : ℤ)))) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))) + (shared15 p)) - (shared25 p)))
end DiophantineConsistency.SharingSeed16Degree112
