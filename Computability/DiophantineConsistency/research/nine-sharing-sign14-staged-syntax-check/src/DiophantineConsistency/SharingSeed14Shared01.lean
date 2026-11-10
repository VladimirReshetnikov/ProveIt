import DiophantineConsistency.SharingSeed14Shared00

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def shared05 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared06 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared07 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared02 p) + ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))
def shared08 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared09 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared04 p) * ((Expr.var 1) + (Expr.constant (1 : ℤ))))
end DiophantineConsistency.SharingSeed14Degree124
