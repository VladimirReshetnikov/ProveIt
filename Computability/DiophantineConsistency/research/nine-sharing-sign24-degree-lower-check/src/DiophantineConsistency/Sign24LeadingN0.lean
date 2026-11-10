import DiophantineConsistency.Sign24CurrentExpressionDef

/-! SOURCE-ONLY: the exact N0 residual and its diagonal specialization. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24LeadingN0

def n0 : Expr (Fin 25) :=
  Expr.var 20 * Expr.var 20 -
    (Expr.var 16 * Expr.var 17) *
      (Expr.var 16 * Expr.var 17 + ((Expr.var 11 + Expr.constant 1) +
        (Expr.var 12 + Expr.constant 1))) - Expr.constant 1

theorem n0_row (p : Fin 4 → ℤ) :
    ((SharingSeed24Octic.remainingResiduals p).drop 6).head? = some n0 := by rfl

def axis {R : Type*} [CommRing R] (t : R) (i : Fin 25) : R :=
  if i = 0 then 1 else if i = 16 ∨ i = 17 then t else 0

theorem n0_axis {R : Type*} [CommRing R] (t : R) :
    n0.evalRing (axis t) = -t^4 - 2*t^2 - 1 := by
  simp only [n0, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, axis]
  norm_num
  ring
end DiophantineConsistency.Sign24LeadingN0
#print axioms DiophantineConsistency.Sign24LeadingN0.n0_row
#print axioms DiophantineConsistency.Sign24LeadingN0.n0_axis
