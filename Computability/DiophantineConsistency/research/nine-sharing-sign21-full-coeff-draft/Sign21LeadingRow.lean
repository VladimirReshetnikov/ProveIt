import DiophantineConsistency.Sign21CurrentExpressionDef

/-! SOURCE-ONLY: the septic axis residual in the sign21 seed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21LeadingRow

def q : Expr (Fin 22) :=
  (Expr.var 6 + Expr.constant 1) * (Expr.var 17 * (Expr.var 17 + Expr.constant 2))

def leading : Expr (Fin 22) :=
  (Expr.var 13 + Expr.constant 1) * (Expr.var 13 + Expr.constant 1) -
    (q * q) * Expr.var 21 - Expr.constant 1

theorem leading_row (p : Fin 4 → ℤ) :
    ((SharingSeed21Degree14.remainingResiduals p).drop 9).head? = some leading := by rfl

def axis {R : Type*} [CommRing R] (t : R) (i : Fin 22) : R :=
  if i = 0 then 1 else if i = 6 ∨ i = 17 ∨ i = 21 then t else 0

theorem leading_axis {R : Type*} [CommRing R] (t : R) :
    leading.evalRing (axis t) = -t^7 - 6*t^6 - 13*t^5 - 12*t^4 - 4*t^3 := by
  have h13 : axis t (13 : Fin 22) = 0 := by rfl
  have h6 : axis t (6 : Fin 22) = t := by rfl
  have h17 : axis t (17 : Fin 22) = t := by rfl
  have h21 : axis t (21 : Fin 22) = t := by rfl
  simp only [leading, q, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, h13, h6, h17, h21,
    Int.cast_ofNat, Int.cast_one]
  ring
end DiophantineConsistency.Sign21LeadingRow
#print axioms DiophantineConsistency.Sign21LeadingRow.leading_row
#print axioms DiophantineConsistency.Sign21LeadingRow.leading_axis
