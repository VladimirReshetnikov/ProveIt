import DiophantineConsistency.Sign23CurrentExpressionDef

/-! SOURCE-ONLY: the two quartic axis residuals in the sign23 seed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23LeadingRows

def n0 : Expr (Fin 24) :=
  Expr.var 19 * Expr.var 19 -
    (Expr.var 16 * Expr.var 17) *
      (Expr.var 16 * Expr.var 17 + ((Expr.var 11 + Expr.constant 1) +
        (Expr.var 12 + Expr.constant 1))) - Expr.constant 1

def delta : Expr (Fin 24) :=
  (Expr.var 16 + Expr.var 15) * (Expr.var 16 + Expr.var 15) +
    (Expr.constant 4 * (Expr.var 16 + Expr.var 15) + Expr.constant 3)

def dc2 : Expr (Fin 24) :=
  Expr.var 18 * (Expr.var 18 + Expr.constant 2) -
    delta * ((Expr.var 17 + (Expr.var 11 + Expr.constant 1)) *
      (Expr.var 17 + (Expr.var 11 + Expr.constant 1)))

theorem n0_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 5).head? = some n0 := by rfl

theorem dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed23Octic.remainingResiduals p).drop 3).head? = some dc2 := by rfl

def axis {R : Type*} [CommRing R] (t : R) (i : Fin 24) : R :=
  if i = 0 then 1 else if i = 16 ∨ i = 17 then t else 0

theorem n0_axis {R : Type*} [CommRing R] (t : R) :
    n0.evalRing (axis t) = -t^4 - 2*t^2 - 1 := by
  have h19 : axis t (19 : Fin 24) = 0 := by rfl
  have h16 : axis t (16 : Fin 24) = t := by rfl
  have h17 : axis t (17 : Fin 24) = t := by rfl
  have h11 : axis t (11 : Fin 24) = 0 := by rfl
  have h12 : axis t (12 : Fin 24) = 0 := by rfl
  simp only [n0, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, h19, h16, h17, h11, h12,
    Int.cast_one]
  ring

theorem dc2_axis {R : Type*} [CommRing R] (t : R) :
    dc2.evalRing (axis t) = -t^4 - 6*t^3 - 12*t^2 - 10*t - 3 := by
  have h18 : axis t (18 : Fin 24) = 0 := by rfl
  have h16 : axis t (16 : Fin 24) = t := by rfl
  have h15 : axis t (15 : Fin 24) = 0 := by rfl
  have h17 : axis t (17 : Fin 24) = t := by rfl
  have h11 : axis t (11 : Fin 24) = 0 := by rfl
  simp only [dc2, delta, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, h18, h16, h15, h17, h11,
    Int.cast_ofNat, Int.cast_one]
  ring
end DiophantineConsistency.Sign23LeadingRows
#print axioms DiophantineConsistency.Sign23LeadingRows.n0_row
#print axioms DiophantineConsistency.Sign23LeadingRows.dc2_row
#print axioms DiophantineConsistency.Sign23LeadingRows.n0_axis
#print axioms DiophantineConsistency.Sign23LeadingRows.dc2_axis
