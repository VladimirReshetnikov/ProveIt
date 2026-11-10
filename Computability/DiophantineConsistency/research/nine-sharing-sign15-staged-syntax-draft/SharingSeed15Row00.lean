import DiophantineConsistency.SharingSeed15Shared07

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed15Degree124
def row00 (p : Fin 4 → ℤ) : Expr (Fin 16) :=
  ((shared37 p) - ((shared36 p) * ((shared17 p) * (shared17 p))))
end DiophantineConsistency.SharingSeed15Degree124
