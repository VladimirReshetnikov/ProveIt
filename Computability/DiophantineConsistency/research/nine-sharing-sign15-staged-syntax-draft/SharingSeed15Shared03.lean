import DiophantineConsistency.SharingSeed15Shared02

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def shared15 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared03 p) * (shared12 p))
def shared16 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (shared13 p))
def shared17 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared16 p) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))
def shared18 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared05 p) * (shared13 p))
def shared19 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared17 p) * ((Expr.var 7) + (Expr.constant (1 : ℤ))))
end DiophantineConsistency.SharingSeed15Degree124
