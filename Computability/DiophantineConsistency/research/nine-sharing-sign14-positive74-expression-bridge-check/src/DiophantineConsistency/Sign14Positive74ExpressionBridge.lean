import DiophantineConsistency.Sign14Positive74RowsInner

/-! SOURCE-ONLY: proposed whole-expression positive-to-natural evaluation. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14Positive74ExpressionBridge
variable {R : Type*} [CommRing R] (p : Fin 4 → ℤ) (v : Fin 14 → R)

theorem eval_shift : (Sign14Positive74.expression p).evalRing (fun i => v i + 1) =
    (Sign14Optimized86Expression.expression p).evalRing v := by
  unfold Sign14Optimized86Expression.expression
  rw [Sign32GenericRemoveInput.eval_removeInput]
  simp only [Sign14Positive74.expression, Sign14Optimized86.seed, Expr.evalRing_add,
    Expr.evalRing_mul, ModelJonesSyntax.evalRing_sumExpressions, List.map_map,
    List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Sign14Positive74RowsOuter.row00_eval, Sign14Positive74RowsInner.row01_eval,
    Sign14Positive74Row02.row_eval, Sign14Positive74RowsInner.row03_eval,
    Sign14Positive74RowsOuter.row04_eval] <;> ring
end DiophantineConsistency.Sign14Positive74ExpressionBridge
#print axioms DiophantineConsistency.Sign14Positive74ExpressionBridge.eval_shift
