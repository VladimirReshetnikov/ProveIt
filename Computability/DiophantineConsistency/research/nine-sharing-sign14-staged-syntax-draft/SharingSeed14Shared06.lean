import DiophantineConsistency.SharingSeed14Shared05

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def shared30 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared21 p) + (shared14 p))
def shared31 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared23 p) * (shared17 p))
def shared32 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared07 p) + (shared31 p))
def shared33 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared23 p) * (shared23 p))
def shared34 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared25 p) - (shared27 p))
end DiophantineConsistency.SharingSeed14Degree124
