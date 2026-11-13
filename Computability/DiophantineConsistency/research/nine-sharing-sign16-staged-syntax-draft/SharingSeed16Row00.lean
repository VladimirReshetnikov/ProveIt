import DiophantineConsistency.SharingSeed16Shared07

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def row00 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared34 p) - ((shared33 p) * ((shared18 p) * (shared18 p))))
end DiophantineConsistency.SharingSeed16Degree112
