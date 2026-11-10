import DiophantineConsistency.NineFreshJones

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed17Degree96
def shared00 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))
def shared01 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))
def shared02 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  ((Expr.var 9) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared03 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ))))
def shared04 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  ((Expr.constant (p 2)) + (shared00 p))
end DiophantineConsistency.SharingSeed17Degree96
