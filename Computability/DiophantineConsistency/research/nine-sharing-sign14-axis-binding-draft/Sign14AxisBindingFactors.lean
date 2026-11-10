import DiophantineConsistency.Sign14AxisBindingBase

/-! SOURCE-ONLY: dominant and middle root factors. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisBinding
open SharingSeed14Degree124 Sign17UnivariateDegree Sign17AxisDegreeBase
  Sign17AxisDegreeRoot Sign17AxisDegreeScale

theorem shared31_axis (p : Fin 4 → ℤ) :
    (shared31 p).evalRing axis = dominant (p 0) := by
  simp only [shared31, shared23, shared18, shared05, shared13, shared12,
    shared08, shared17, shared16, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, axis01, axis08, axis09, axis11, axis12,
    dominant, e, y, cube, u, twice, affine, shift,
    polynomial_C_eq_cast, Int.cast_ofNat, Int.cast_one, two_mul, mul_assoc]
  all_goals rfl

theorem shared28_axis (p : Fin 4 → ℤ) :
    (shared28 p).evalRing axis = middle (p 0) := by
  simp only [shared28, shared26, shared24, shared23, shared18, shared05,
    shared13, shared12, shared08, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, axis01, axis08, axis09, axis14,
    middle, e, y, cube, affine, shift,
    polynomial_C_eq_cast, Int.cast_ofNat, Int.cast_one, two_mul, mul_assoc]
  all_goals rfl
end DiophantineConsistency.Sign14AxisBinding
#print axioms DiophantineConsistency.Sign14AxisBinding.shared31_axis
#print axioms DiophantineConsistency.Sign14AxisBinding.shared28_axis
