import DiophantineConsistency.SharingSeed14Shared08

/-! SOURCE-ONLY staged residual. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def row00 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared41 p) - ((shared40 p) * ((shared17 p) * (shared17 p))))
end DiophantineConsistency.SharingSeed14Degree124
