import DiophantineConsistency.SharingSeed18Shared03

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed18Degree94
def shared20 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared18 p) + (shared13 p))
def shared21 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((Expr.constant (4 : ℤ)) * (shared20 p))
def shared22 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared21 p) + (Expr.constant (3 : ℤ)))
def shared23 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared19 p) + (shared09 p))
def shared24 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  (((Expr.var 14) + (Expr.constant (1 : ℤ))) * (shared22 p))
end DiophantineConsistency.SharingSeed18Degree94
