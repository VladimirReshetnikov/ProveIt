import DiophantineConsistency.SharingSeed14Shared06

/-! SOURCE-ONLY staged shared syntax. -/
set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
namespace DiophantineConsistency.SharingSeed14Degree124
def shared35 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((((Expr.var 5) + (Expr.constant (1 : ℤ))) * ((Expr.var 5) + (Expr.constant (1 : ℤ)))) * (shared34 p))
def shared36 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared30 p) - (shared27 p))
def shared37 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared35 p) - (shared17 p))
def shared38 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared32 p) + (shared28 p))
def shared39 (p : Fin 4 → ℤ) : Expr (Fin 15) :=
  ((shared38 p) + (Expr.constant (2 : ℤ)))
end DiophantineConsistency.SharingSeed14Degree124
