import DiophantineConsistency.SharingSeed16Shared01

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def shared10 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared05 p) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))
def shared11 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared07 p) + ((Expr.var 3) + (Expr.constant (1 : ℤ))))
def shared12 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((((Expr.var 2) + (Expr.constant (1 : ℤ))) + ((Expr.var 3) + (Expr.constant (1 : ℤ)))) * (shared09 p))
def shared13 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared09 p) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared14 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  (((Expr.var 8) + (Expr.constant (1 : ℤ))) * (shared13 p))
end DiophantineConsistency.SharingSeed16Degree112
