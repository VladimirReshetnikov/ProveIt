import DiophantineConsistency.SharingSeed16Shared02

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed16Degree112
def shared15 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared11 p) - (shared02 p))
def shared16 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared04 p) * (shared13 p))
def shared17 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((((Expr.var 11) + (Expr.constant (1 : ℤ))) + ((Expr.var 12) + (Expr.constant (1 : ℤ)))) * (shared14 p))
def shared18 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared17 p) + ((Expr.var 11) + (Expr.constant (1 : ℤ))))
def shared19 (p : Fin 4 → ℤ) : Expr (Fin 17) :=
  ((shared06 p) * (shared14 p))
end DiophantineConsistency.SharingSeed16Degree112
