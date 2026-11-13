import DiophantineConsistency.SharingSeed18Shared06

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed18Degree94
def row00 (p : Fin 4 → ℤ) : Expr (Fin 19) :=
  ((shared32 p) - ((shared31 p) * ((shared17 p) * (shared17 p))))
end DiophantineConsistency.SharingSeed18Degree94
