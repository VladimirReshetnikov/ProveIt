import DiophantineConsistency.SharingSeed17Shared06

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed17Degree96
def row00 (p : Fin 4 → ℤ) : Expr (Fin 18) :=
  ((shared32 p) - ((shared31 p) * ((shared17 p) * (shared17 p))))
end DiophantineConsistency.SharingSeed17Degree96
