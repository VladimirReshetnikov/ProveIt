import DiophantineConsistency.Sign17AxisNaDegree

/-! SOURCE-ONLY: degree bounds for non-Na residuals on the corrected axis. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17AxisOtherDegree
open SharingSeed17Degree96 Sign17UnivariateDegree Sign17AxisRootBinding Sign17SyntaxDegree

attribute [local irreducible] row00 row01 row02 row03 row04 row05 row06 row07

theorem eval_degree_le {σ : Type} (e : Expr σ) (v : σ → P)
    (hv : ∀ i, (v i).natDegree ≤ 1) : (e.evalRing v).natDegree ≤ degree e := by
  induction e with
  | constant z => simp [Expr.evalRing, degree]
  | var i => simpa [Expr.evalRing, degree] using hv i
  | add a b ha hb =>
    exact (Polynomial.natDegree_add_le _ _).trans (max_le_max ha hb)
  | sub a b ha hb =>
    exact (Polynomial.natDegree_sub_le _ _).trans (max_le_max ha hb)
  | mul a b ha hb =>
    exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add ha hb)

theorem axis_degree_le (i : Fin 18) : (axis i).natDegree ≤ 1 := by
  by_cases h0 : i = 0
  · simp [axis, h0]
  · by_cases h17 : i = 17 <;> simp [axis, h0, h17]

def otherRows (p : Fin 4 → ℤ) : List (Expr (Fin 18)) :=
  [row00 p, row01 p, row02 p, row03 p, row04 p, row05 p, row07 p]

theorem other_rows_syntax_degree (p : Fin 4 → ℤ) (e : Expr (Fin 18))
    (he : e ∈ otherRows p) : degree e ≤ 46 := by
  have h0 := row00_degree p
  have h1 := row01_degree p
  have h2 := row02_degree p
  have h3 := row03_degree p
  have h4 := row04_degree p
  have h5 := row05_degree p
  have h7 := row07_degree p
  simp only [otherRows, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

theorem other_rows_axis_degree (p : Fin 4 → ℤ) (e : Expr (Fin 18))
    (he : e ∈ otherRows p) : (e.evalRing axis).natDegree ≤ 46 :=
  (eval_degree_le e axis axis_degree_le).trans (other_rows_syntax_degree p e he)

end DiophantineConsistency.Sign17AxisOtherDegree
#print axioms DiophantineConsistency.Sign17AxisOtherDegree.eval_degree_le
#print axioms DiophantineConsistency.Sign17AxisOtherDegree.axis_degree_le
#print axioms DiophantineConsistency.Sign17AxisOtherDegree.other_rows_syntax_degree
#print axioms DiophantineConsistency.Sign17AxisOtherDegree.other_rows_axis_degree
