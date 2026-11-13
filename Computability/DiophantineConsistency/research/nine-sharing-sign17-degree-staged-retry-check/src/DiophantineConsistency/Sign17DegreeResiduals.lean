import DiophantineConsistency.Sign17RowDegrees01
import DiophantineConsistency.Sign17DegreeStructural

/-! SOURCE-ONLY: compose staged row bounds into residual bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree
open SharingSeed17Degree96
attribute [local irreducible] row00 row01 row02 row03 row04 row05 row06 row07

theorem first_degree_le (p : Fin 4 → ℤ) :
    degree (SharingSeed17Degree96.firstResidual p) ≤ 48 := by
  change degree (row00 p) ≤ 48
  have h := row00_degree p
  omega

theorem remaining_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 18))
    (he : e ∈ SharingSeed17Degree96.remainingResiduals p) : degree e ≤ 48 := by
  have h1 := row01_degree p
  have h2 := row02_degree p
  have h3 := row03_degree p
  have h4 := row04_degree p
  have h5 := row05_degree p
  have h6 := row06_degree p
  have h7 := row07_degree p
  simp only [SharingSeed17Degree96.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
end DiophantineConsistency.Sign17SyntaxDegree
#print axioms DiophantineConsistency.Sign17SyntaxDegree.first_degree_le
#print axioms DiophantineConsistency.Sign17SyntaxDegree.remaining_degree_le
