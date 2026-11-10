import DiophantineConsistency.SharingSeed14Shared04

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def shared25 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared19 p) + (shared14 p))
def shared26 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared24 p) + (Expr.constant (3 : ℤ)))
def shared27 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared22 p) + (shared09 p))
def shared28 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (shared26 p))
def shared29 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared18 p) * (shared16 p))
end DiophantineConsistency.SharingSeed14Degree124
