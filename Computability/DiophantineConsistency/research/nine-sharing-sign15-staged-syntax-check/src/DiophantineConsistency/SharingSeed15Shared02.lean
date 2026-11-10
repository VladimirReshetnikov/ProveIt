import DiophantineConsistency.SharingSeed15Shared01

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def shared10 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared06 p) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))
def shared11 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * (shared08 p))
def shared12 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared08 p) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared13 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (shared12 p))
def shared14 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared10 p) - (shared01 p))
end DiophantineConsistency.SharingSeed15Degree124
