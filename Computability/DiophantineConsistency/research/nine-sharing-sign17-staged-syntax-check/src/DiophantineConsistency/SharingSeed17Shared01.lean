import DiophantineConsistency.SharingSeed17Shared00

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed17Degree96
def shared05 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  (((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared06 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared07 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  ((shared02 p) + ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))
def shared08 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared09 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  ((shared04 p) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))
end DiophantineConsistency.SharingSeed17Degree96
