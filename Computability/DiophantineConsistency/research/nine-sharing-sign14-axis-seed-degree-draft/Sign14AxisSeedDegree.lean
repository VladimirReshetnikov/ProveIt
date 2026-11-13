import DiophantineConsistency.Sign14AxisNoncancel

/-! SOURCE-ONLY: bind noncancellation to the actual staged seed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisSeedDegree
open SharingSeed14Degree124 Sign17UnivariateDegree Sign14AxisBinding
  Sign14AxisOtherDegree Sign14AxisNoncancel

attribute [local irreducible] row00 row01 row02 row03 row04

theorem seed_axis (p : Fin 4 → ℤ) :
    (seed p).evalRing axis =
      ((row03 p).evalRing axis * (row03 p).evalRing axis) + otherSum p := by
  simp only [seed, firstResidual, remainingResiduals, Expr.evalRing_add,
    Expr.evalRing_mul, ModelJonesSyntax.evalRing_sumExpressions, List.map_map,
    Function.comp_apply, otherSum, otherRows, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

theorem seed_axis_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    ((seed p).evalRing axis).natDegree = 124 := by
  rw [seed_axis]
  exact combined_degree p hz

end DiophantineConsistency.Sign14AxisSeedDegree
#print axioms DiophantineConsistency.Sign14AxisSeedDegree.seed_axis
#print axioms DiophantineConsistency.Sign14AxisSeedDegree.seed_axis_degree
