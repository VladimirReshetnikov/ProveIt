import DiophantineConsistency.SharingSeed18Shared05

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed18Degree94
def shared30 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared29 p) + (Expr.constant (2 : ℤ)))
def shared31 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared28 p) + (shared22 p))
def shared32 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared29 p) * (shared30 p))
def shared33 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (shared32 p))
def shared34 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared33 p) * (shared33 p))
end DiophantineConsistency.SharingSeed18Degree94
