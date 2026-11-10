import DiophantineConsistency.Sign17AxisNoncancel

/-! SOURCE-ONLY: bind noncancellation to the actual staged seed. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisSeedDegree
open SharingSeed17Degree96 Sign17UnivariateDegree Sign17AxisRootBinding
  Sign17AxisOtherDegree Sign17AxisNoncancel

attribute [local irreducible] row00 row01 row02 row03 row04 row05 row06 row07

theorem seed_axis (p : Fin 4 → ℤ) :
    (seed p).evalRing axis =
      ((row06 p).evalRing axis * (row06 p).evalRing axis) + otherSum p := by
  simp only [seed, firstResidual, remainingResiduals, Expr.evalRing_add,
    Expr.evalRing_mul, ModelJonesSyntax.evalRing_sumExpressions, List.map_map,
    Function.comp_apply, otherSum, otherRows, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil]
  ring

theorem seed_axis_degree (p : Fin 4 → ℤ) (hz : p 0 ≠ 0) :
    ((seed p).evalRing axis).natDegree = 96 := by
  rw [seed_axis]
  exact combined_degree p hz

end DiophantineConsistency.Sign17AxisSeedDegree
#print axioms DiophantineConsistency.Sign17AxisSeedDegree.seed_axis
#print axioms DiophantineConsistency.Sign17AxisSeedDegree.seed_axis_degree
