import DiophantineConsistency.SharingSeed15Shared04

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def shared25 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared20 p) + (shared09 p))
def shared26 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (shared24 p))
def shared27 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared18 p) * (shared16 p))
def shared28 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared21 p) * (shared17 p))
def shared29 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared07 p) + (shared28 p))
end DiophantineConsistency.SharingSeed15Degree124
