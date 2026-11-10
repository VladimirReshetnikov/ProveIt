import DiophantineConsistency.SharingSeed15Shared05

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def shared30 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared21 p) * (shared21 p))
def shared31 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared23 p) - (shared25 p))
def shared32 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (shared31 p))
def shared33 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared32 p) - (shared17 p))
def shared34 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared29 p) + (shared26 p))
end DiophantineConsistency.SharingSeed15Degree124
