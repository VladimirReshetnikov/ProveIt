import DiophantineConsistency.SharingSeed15Shared03

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def shared20 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared15 p) + (shared11 p))
def shared21 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared18 p) + (shared13 p))
def shared22 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((Expr.constant (4 : ℤ)) * (shared21 p))
def shared23 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared19 p) + (shared14 p))
def shared24 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared22 p) + (Expr.constant (3 : ℤ)))
end DiophantineConsistency.SharingSeed15Degree124
