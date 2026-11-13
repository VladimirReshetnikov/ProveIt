import DiophantineConsistency.Sign14AxisGenericDegree
import DiophantineConsistency.Sign14DegreeCompose

/-! SOURCE-ONLY: staged sign14 axis bindings; not yet Lean checked. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisBinding
open SharingSeed14Degree124 Sign17UnivariateDegree Sign17AxisDegreeBase
  Sign17AxisDegreeRoot Sign17AxisDegreeScale

def axis (i : Fin 15) : P := if i = 0 then 1 else Polynomial.X

theorem axis01 : axis 1 = Polynomial.X := rfl
theorem axis06 : axis 6 = Polynomial.X := rfl
theorem axis08 : axis 8 = Polynomial.X := rfl
theorem axis09 : axis 9 = Polynomial.X := rfl
theorem axis11 : axis 11 = Polynomial.X := rfl
theorem axis12 : axis 12 = Polynomial.X := rfl
theorem axis14 : axis 14 = Polynomial.X := rfl
theorem axis00 : axis 0 = 1 := rfl

theorem polynomial_C_eq_cast (z : ℤ) : (Polynomial.C z : P) = (z : P) := by
  simpa using (Polynomial.C_eq_intCast (R := ℤ) z)

theorem shared07_axis (p : Fin 4 → ℤ) :
    (shared07 p).evalRing axis = low (p 0) := by
  simp only [shared07, shared02, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, axis01, axis09,
    low, affine, shift, polynomial_C_eq_cast, Int.cast_one, two_mul, mul_assoc]
  all_goals rfl
end DiophantineConsistency.Sign14AxisBinding
#print axioms DiophantineConsistency.Sign14AxisBinding.shared07_axis
