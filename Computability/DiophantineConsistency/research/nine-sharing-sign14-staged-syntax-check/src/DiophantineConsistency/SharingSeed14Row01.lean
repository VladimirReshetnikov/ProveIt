import DiophantineConsistency.SharingSeed14Shared08

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def row01 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((((shared36 p) * (shared36 p)) - ((shared29 p) * ((shared29 p) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ))))))) - (Expr.constant (1 : ℤ)))
end DiophantineConsistency.SharingSeed14Degree124
