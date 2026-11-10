import DiophantineConsistency.SharingSeed16Shared06

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def shared35 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  (((Expr.var 6) + (Expr.constant (1 : ℤ))) * (shared34 p))
def shared36 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared35 p) * (shared35 p))
end DiophantineConsistency.SharingSeed16Degree112
