import DiophantineConsistency.Sign17AxisBindingFactors

set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisRootBinding
open SharingSeed17Degree96 Sign17UnivariateDegree Sign17AxisDegreeBase
  Sign17AxisDegreeRoot Sign17AxisDegreeScale

theorem shared29_axis (p : Fin 4 → ℤ) :
    (shared29 p).evalRing axis = root (p 0) := by
  simp only [shared29, shared27, Expr.evalRing_add, shared07_axis,
    shared26_axis, shared24_axis, root]

theorem shared33_axis (p : Fin 4 → ℤ) :
    (shared33 p).evalRing axis = scale (p 0) := by
  simp only [shared33, shared32, shared30, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, shared29_axis, axis06,
    Int.cast_ofNat, Int.cast_one, scale, shift]
  all_goals rfl


end DiophantineConsistency.Sign17AxisRootBinding
#print axioms DiophantineConsistency.Sign17AxisRootBinding.shared29_axis
#print axioms DiophantineConsistency.Sign17AxisRootBinding.shared33_axis
