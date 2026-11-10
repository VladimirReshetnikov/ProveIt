import DiophantineConsistency.Sign14RowDegree04
import DiophantineConsistency.Sign14DegreeStructural

/-! SOURCE-ONLY: compositional residual bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign14SyntaxDegree
open SharingSeed14Degree124
attribute [local irreducible] row00 row01 row02 row03 row04

theorem first_degree_le (p : Fin 4 → ℤ) :
    degree (SharingSeed14Degree124.firstResidual p) ≤ 62 := by
  change degree (row00 p) ≤ 62
  have h := row00_degree p
  omega

theorem remaining_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 15))
    (he : e ∈ SharingSeed14Degree124.remainingResiduals p) : degree e ≤ 62 := by
  have h1 := row01_degree p
  have h2 := row02_degree p
  have h3 := row03_degree p
  have h4 := row04_degree p
  simp only [SharingSeed14Degree124.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl <;> omega
end DiophantineConsistency.Sign14SyntaxDegree
#print axioms DiophantineConsistency.Sign14SyntaxDegree.first_degree_le
#print axioms DiophantineConsistency.Sign14SyntaxDegree.remaining_degree_le
