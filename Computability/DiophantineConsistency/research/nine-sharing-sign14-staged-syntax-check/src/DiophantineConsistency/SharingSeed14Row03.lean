import DiophantineConsistency.SharingSeed14Shared08

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def row03 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((shared43 p) * ((((Expr.var 13) + (Expr.constant (1 : ℤ))) * ((Expr.var 13) + (Expr.constant (1 : ℤ)))) - ((shared37 p) * (shared37 p))))) - (Expr.constant (1 : ℤ)))
end DiophantineConsistency.SharingSeed14Degree124
