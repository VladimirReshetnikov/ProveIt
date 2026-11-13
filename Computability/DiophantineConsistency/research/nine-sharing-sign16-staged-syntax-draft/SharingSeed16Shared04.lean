import DiophantineConsistency.SharingSeed16Shared03

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def shared20 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared01 p) - (shared18 p))
def shared21 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared16 p) + (shared12 p))
def shared22 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared19 p) + (shared14 p))
def shared23 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((Expr.constant (4 : ℤ)) * (shared22 p))
def shared24 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared23 p) + (Expr.constant (3 : ℤ)))
end DiophantineConsistency.SharingSeed16Degree112
