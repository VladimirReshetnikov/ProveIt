import DiophantineConsistency.Sign14AxisInnerBinding
import DiophantineConsistency.Sign14AxisGenericNaDegree

/-! SOURCE-ONLY: actual staged row binding to generic Na polynomial. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisNaBinding
open SharingSeed14Degree124 Sign17UnivariateDegree Sign17AxisDegreeBase
  Sign17AxisDegreeRoot Sign17AxisDegreeScale Sign14AxisBinding
  Sign14AxisInnerBinding Sign14AxisGenericNaDegree

theorem axis13 : axis 13 = Polynomial.X := rfl

theorem row03_axis (p : Fin 4 → ℤ) :
    (row03 p).evalRing axis = row (p 0) ((shared14 p).evalRing axis)
      ((shared27 p).evalRing axis) := by
  simp only [row03, shared43, Expr.evalRing_add, Expr.evalRing_sub,
    Expr.evalRing_mul, Expr.evalRing_constant, Expr.evalRing_var, shared42_axis,
    shared37_axis, axis13, Int.cast_one, row, shift]
  all_goals rfl

theorem row03_axis_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    ((row03 p).evalRing axis).natDegree = 62 := by
  rw [row03_axis]
  exact row_degree (p 0) hz _ _ (correction_degree p) (rank_degree p)
end DiophantineConsistency.Sign14AxisNaBinding
#print axioms DiophantineConsistency.Sign14AxisNaBinding.row03_axis
#print axioms DiophantineConsistency.Sign14AxisNaBinding.row03_axis_degree
