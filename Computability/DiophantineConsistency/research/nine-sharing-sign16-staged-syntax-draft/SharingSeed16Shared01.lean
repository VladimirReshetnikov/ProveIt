import DiophantineConsistency.SharingSeed16Shared00

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def shared05 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((Expr.constant (p 2)) + (shared00 p))
def shared06 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  (((Expr.var 9) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared07 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
def shared08 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared03 p) + ((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))))
def shared09 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))) * (((Expr.constant (p 0)) * ((Expr.var 1) + (Expr.constant (1 : ℤ)))) + (Expr.constant (1 : ℤ))))
end DiophantineConsistency.SharingSeed16Degree112
