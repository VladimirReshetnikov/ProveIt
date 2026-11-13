import DiophantineConsistency.Sign20CurrentExpressionDef

/-! SOURCE-ONLY: two port-dependent degree-ten axis residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20LeadingRows

def e (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  (Expr.var 9 + Expr.constant 1) *
    (Expr.constant (p 0) * (Expr.var 1 + Expr.constant 1) + Expr.constant 1) * Expr.var 15

def u : Expr (Fin 21) :=
  ((Expr.var 11 + Expr.constant 1) + (Expr.var 12 + Expr.constant 1)) * Expr.var 15

def a : Expr (Fin 21) := u + (Expr.var 11 + Expr.constant 1)

def delta (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  (e p + Expr.var 15) * (e p + Expr.var 15) +
    (Expr.constant 4 * (e p + Expr.var 15) + Expr.constant 3)

def dc2 (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  Expr.var 16 * (Expr.var 16 + Expr.constant 2) - delta p * (a * a)

def n0 (p : Fin 4 → ℤ) : Expr (Fin 21) :=
  Expr.var 17 * Expr.var 17 - (e p * u) *
    (e p * u + ((Expr.var 11 + Expr.constant 1) +
      (Expr.var 12 + Expr.constant 1))) - Expr.constant 1

theorem dc2_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 1).head? = some (dc2 p) := by rfl

theorem n0_row (p : Fin 4 → ℤ) :
    ((SharingSeed20Degree20.remainingResiduals p).drop 3).head? = some (n0 p) := by rfl

def axis {R : Type*} [CommRing R] (t : R) (i : Fin 21) : R :=
  if i = 0 then 1 else if i = 1 ∨ i = 9 ∨ i = 11 ∨ i = 15 then t else 0

theorem dc2_axis {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (t : R) :
    (dc2 p).evalRing (axis t) =
      -((t*(t+1)*((p 0 : R)*(t+1)+1)+t)^2 +
        4*(t*(t+1)*((p 0 : R)*(t+1)+1)+t) + 3) * (t^2+3*t+1)^2 := by
  have h16 : axis t (16 : Fin 21) = 0 := by rfl
  have h15 : axis t (15 : Fin 21) = t := by rfl
  have h12 : axis t (12 : Fin 21) = 0 := by rfl
  have h11 : axis t (11 : Fin 21) = t := by rfl
  have h9 : axis t (9 : Fin 21) = t := by rfl
  have h1 : axis t (1 : Fin 21) = t := by rfl
  simp only [dc2, delta, e, a, u, Expr.evalRing_sub, Expr.evalRing_mul,
    Expr.evalRing_add, Expr.evalRing_var, Expr.evalRing_constant, h16, h15, h12,
    h11, h9, h1, Int.cast_ofNat, Int.cast_one]
  ring

theorem n0_axis {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (t : R) :
    (n0 p).evalRing (axis t) =
      -(t*(t+1)*((p 0 : R)*(t+1)+1)*((t+2)*t)) *
        (t*(t+1)*((p 0 : R)*(t+1)+1)*((t+2)*t)+(t+2)) - 1 := by
  have h17 : axis t (17 : Fin 21) = 0 := by rfl
  have h15 : axis t (15 : Fin 21) = t := by rfl
  have h12 : axis t (12 : Fin 21) = 0 := by rfl
  have h11 : axis t (11 : Fin 21) = t := by rfl
  have h9 : axis t (9 : Fin 21) = t := by rfl
  have h1 : axis t (1 : Fin 21) = t := by rfl
  simp only [n0, e, u, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_add,
    Expr.evalRing_var, Expr.evalRing_constant, h17, h15, h12, h11, h9, h1,
    Int.cast_ofNat, Int.cast_one]
  ring
end DiophantineConsistency.Sign20LeadingRows
#print axioms DiophantineConsistency.Sign20LeadingRows.dc2_row
#print axioms DiophantineConsistency.Sign20LeadingRows.n0_row
#print axioms DiophantineConsistency.Sign20LeadingRows.dc2_axis
#print axioms DiophantineConsistency.Sign20LeadingRows.n0_axis
