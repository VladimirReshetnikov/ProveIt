import DiophantineConsistency.Sign17AxisBindingBase

set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisRootBinding
open SharingSeed17Degree96 Sign17UnivariateDegree Sign17AxisDegreeBase
  Sign17AxisDegreeRoot Sign17AxisDegreeScale

theorem shared26_axis (p : Fin 4 → ℤ) :
    (shared26 p).evalRing axis = dominant (p 0) := by
  simp only [shared26, shared20, shared18, shared05, shared13, shared12,
    shared08, shared17, shared16, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, axis01, axis08, axis09, axis11, axis12,
    dominant, e, y, cube, u, twice, affine, shift,
    polynomial_C_eq_cast, Int.cast_ofNat, Int.cast_one, two_mul, mul_assoc]
  all_goals rfl

theorem shared24_axis (p : Fin 4 → ℤ) :
    (shared24 p).evalRing axis = middle (p 0) := by
  simp only [shared24, shared22, shared21, shared20, shared18, shared05,
    shared13, shared12, shared08, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, axis01, axis08, axis09, axis14,
    middle, e, y, cube, affine, shift,
    polynomial_C_eq_cast, Int.cast_ofNat, Int.cast_one, two_mul, mul_assoc]
  all_goals rfl


end DiophantineConsistency.Sign17AxisRootBinding
#print axioms DiophantineConsistency.Sign17AxisRootBinding.shared26_axis
#print axioms DiophantineConsistency.Sign17AxisRootBinding.shared24_axis
