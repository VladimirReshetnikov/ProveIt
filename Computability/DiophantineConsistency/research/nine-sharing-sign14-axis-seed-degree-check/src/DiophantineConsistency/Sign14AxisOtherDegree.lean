import DiophantineConsistency.Sign14AxisNaBinding

/-! SOURCE-ONLY: other staged rows have smaller axis degree. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14AxisOtherDegree
open SharingSeed14Degree124 Sign17UnivariateDegree Sign14AxisBinding
  Sign14AxisInnerBinding Sign14SyntaxDegree
attribute [local irreducible] row00 row01 row02 row03 row04

def otherRows (p : Fin 4 → ℤ) : List (Expr (Fin 15)) :=
  [row00 p, row01 p, row02 p, row04 p]

theorem other_rows_syntax_degree (p : Fin 4 → ℤ) (e : Expr (Fin 15))
    (he : e ∈ otherRows p) : degree e ≤ 46 := by
  have h0 := row00_degree p
  have h1 := row01_degree p
  have h2 := row02_degree p
  have h4 := row04_degree p
  simp only [otherRows, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> omega

theorem other_rows_axis_degree (p : Fin 4 → ℤ) (e : Expr (Fin 15))
    (he : e ∈ otherRows p) : (e.evalRing axis).natDegree ≤ 46 :=
  (eval_degree_le e axis axis_degree_le).trans (other_rows_syntax_degree p e he)
end DiophantineConsistency.Sign14AxisOtherDegree
#print axioms DiophantineConsistency.Sign14AxisOtherDegree.other_rows_syntax_degree
#print axioms DiophantineConsistency.Sign14AxisOtherDegree.other_rows_axis_degree
