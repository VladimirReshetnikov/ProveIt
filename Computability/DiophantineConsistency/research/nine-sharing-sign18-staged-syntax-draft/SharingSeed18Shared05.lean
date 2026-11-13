import DiophantineConsistency.SharingSeed18Shared04

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed18Degree94
def shared25 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared18 p) * (shared16 p))
def shared26 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared20 p) * (shared17 p))
def shared27 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared07 p) + (shared26 p))
def shared28 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared20 p) * (shared20 p))
def shared29 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared27 p) + (shared24 p))
end DiophantineConsistency.SharingSeed18Degree94
