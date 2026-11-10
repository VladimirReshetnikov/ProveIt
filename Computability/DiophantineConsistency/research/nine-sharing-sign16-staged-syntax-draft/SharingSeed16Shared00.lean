import DiophantineConsistency.NineFreshJones

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def shared00 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (Expr.constant (p 3)))
def shared01 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (Expr.var 16))
def shared02 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * ((Expr.var 2) + (Expr.constant (1 : ℤ))))
def shared03 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((Expr.var 9) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared04 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) - ((Expr.var 2) + (Expr.constant (1 : ℤ))))
end DiophantineConsistency.SharingSeed16Degree112
