import DiophantineConsistency.SharingSeed14Shared03

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def shared20 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared18 p) * ((Expr.var 10) + (Expr.constant (1 : ℤ))))
def shared21 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared20 p) + (((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))))
def shared22 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared15 p) + (shared11 p))
def shared23 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared18 p) + (shared13 p))
def shared24 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((Expr.constant (4 : ℤ)) * (shared23 p))
end DiophantineConsistency.SharingSeed14Degree124
