import DiophantineConsistency.SharingSeed14Shared08

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def row04 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((((shared40 p) * (((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ))))) - (shared43 p)) - (shared40 p))
end DiophantineConsistency.SharingSeed14Degree124
