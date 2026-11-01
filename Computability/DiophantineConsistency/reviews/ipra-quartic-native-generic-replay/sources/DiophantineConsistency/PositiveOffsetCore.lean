import DiophantineConsistency.NaturalExpression

/-! Lightweight syntax for the positive-coordinate offset. -/
namespace DiophantineConsistency.PositiveOffsetArithmetic
variable {σ : Type*}
def decrement (e : Expr σ) : Expr σ := e.subst (fun i => .var i - 1)
end DiophantineConsistency.PositiveOffsetArithmetic
