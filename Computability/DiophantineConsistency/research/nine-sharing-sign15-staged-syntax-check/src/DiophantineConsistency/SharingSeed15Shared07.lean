import DiophantineConsistency.SharingSeed15Shared06

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def shared35 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared34 p) + (Expr.constant (2 : ℤ)))
def shared36 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared30 p) + (shared24 p))
def shared37 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared34 p) * (shared35 p))
def shared38 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (shared37 p))
def shared39 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared38 p) * (shared38 p))
end DiophantineConsistency.SharingSeed15Degree124
