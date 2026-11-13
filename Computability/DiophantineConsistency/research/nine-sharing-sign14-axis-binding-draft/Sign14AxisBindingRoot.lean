import DiophantineConsistency.Sign14AxisBindingFactors

/-! SOURCE-ONLY: staged root and scale axis bindings. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisBinding
open SharingSeed14Degree124 Sign17UnivariateDegree Sign17AxisDegreeBase
  Sign17AxisDegreeRoot Sign17AxisDegreeScale

theorem shared38_axis (p : Fin 4 → ℤ) :
    (shared38 p).evalRing axis = root (p 0) := by
  simp only [shared38, shared32, Expr.evalRing_add, shared07_axis,
    shared31_axis, shared28_axis, root]

theorem shared42_axis (p : Fin 4 → ℤ) :
    (shared42 p).evalRing axis = scale (p 0) := by
  simp only [shared42, shared41, shared39, Expr.evalRing_add, Expr.evalRing_mul,
    Expr.evalRing_constant, Expr.evalRing_var, shared38_axis, axis06,
    Int.cast_ofNat, Int.cast_one, scale, shift]
  all_goals exact (mul_assoc _ _ _).symm
end DiophantineConsistency.Sign14AxisBinding
#print axioms DiophantineConsistency.Sign14AxisBinding.shared38_axis
#print axioms DiophantineConsistency.Sign14AxisBinding.shared42_axis
