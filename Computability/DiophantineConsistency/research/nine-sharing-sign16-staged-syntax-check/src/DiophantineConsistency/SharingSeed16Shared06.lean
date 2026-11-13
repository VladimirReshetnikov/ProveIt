import DiophantineConsistency.SharingSeed16Shared05

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def shared30 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared22 p) * (shared22 p))
def shared31 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared29 p) + (shared26 p))
def shared32 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared31 p) + (Expr.constant (2 : ℤ)))
def shared33 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared30 p) + (shared24 p))
def shared34 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared31 p) * (shared32 p))
end DiophantineConsistency.SharingSeed16Degree112
