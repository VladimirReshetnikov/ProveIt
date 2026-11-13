import DiophantineConsistency.SharingSeed16Shared04

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def shared25 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared21 p) + (shared10 p))
def shared26 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (shared24 p))
def shared27 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared19 p) * (shared17 p))
def shared28 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared22 p) * (shared18 p))
def shared29 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared08 p) + (shared28 p))
end DiophantineConsistency.SharingSeed16Degree112
