import DiophantineConsistency.SharingSeed14Shared07

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def shared40 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared33 p) + (shared26 p))
def shared41 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared38 p) * (shared39 p))
def shared42 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (shared41 p))
def shared43 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared42 p) * (shared42 p))
end DiophantineConsistency.SharingSeed14Degree124
