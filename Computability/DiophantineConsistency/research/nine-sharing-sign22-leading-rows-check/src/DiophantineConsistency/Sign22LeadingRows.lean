import DiophantineConsistency.Sign22CurrentExpressionDef

/-! SOURCE-ONLY: two sextic axis residuals in the sign22 seed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22LeadingRows

def u : Expr (Fin 23) :=
  ((Expr.var 11 + Expr.constant 1) + (Expr.var 12 + Expr.constant 1)) * Expr.var 15

def a : Expr (Fin 23) := u + (Expr.var 11 + Expr.constant 1)

def delta : Expr (Fin 23) :=
  (Expr.var 16 + Expr.var 15) * (Expr.var 16 + Expr.var 15) +
    (Expr.constant 4 * (Expr.var 16 + Expr.var 15) + Expr.constant 3)

def dc2 : Expr (Fin 23) :=
  Expr.var 17 * (Expr.var 17 + Expr.constant 2) - delta * (a * a)

def n0 : Expr (Fin 23) :=
  Expr.var 18 * Expr.var 18 - (Expr.var 16 * u) *
    (Expr.var 16 * u + ((Expr.var 11 + Expr.constant 1) +
      (Expr.var 12 + Expr.constant 1))) - Expr.constant 1

theorem dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed22Dodecic.remainingResiduals p).drop 2).head? = some dc2 := by rfl

theorem n0_row (p : Fin 4 → ℤ) :
    ((SharingSeed22Dodecic.remainingResiduals p).drop 4).head? = some n0 := by rfl

def axis {R : Type*} [CommRing R] (t : R) (i : Fin 23) : R :=
  if i = 0 then 1 else if i = 11 ∨ i = 12 ∨ i = 15 ∨ i = 16 then t else 0

theorem dc2_axis {R : Type*} [CommRing R] (t : R) :
    dc2.evalRing (axis t) = -(4*t^2 + 8*t + 3) * (2*t^2 + 3*t + 1)^2 := by
  have h17 : axis t (17 : Fin 23) = 0 := by rfl
  have h16 : axis t (16 : Fin 23) = t := by rfl
  have h15 : axis t (15 : Fin 23) = t := by rfl
  have h11 : axis t (11 : Fin 23) = t := by rfl
  have h12 : axis t (12 : Fin 23) = t := by rfl
  simp only [dc2, delta, a, u, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, h17, h16, h15,
    h11, h12, Int.cast_ofNat, Int.cast_one]
  ring

theorem n0_axis {R : Type*} [CommRing R] (t : R) :
    n0.evalRing (axis t) = -4*t^6 - 4*t^4 - 4*t^3 - 1 := by
  have h18 : axis t (18 : Fin 23) = 0 := by rfl
  have h16 : axis t (16 : Fin 23) = t := by rfl
  have h15 : axis t (15 : Fin 23) = t := by rfl
  have h11 : axis t (11 : Fin 23) = t := by rfl
  have h12 : axis t (12 : Fin 23) = t := by rfl
  simp only [n0, u, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, h18, h16, h15, h11, h12,
    Int.cast_one]
  ring
end DiophantineConsistency.Sign22LeadingRows
#print axioms DiophantineConsistency.Sign22LeadingRows.dc2_row
#print axioms DiophantineConsistency.Sign22LeadingRows.n0_row
#print axioms DiophantineConsistency.Sign22LeadingRows.dc2_axis
#print axioms DiophantineConsistency.Sign22LeadingRows.n0_axis
