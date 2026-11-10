import DiophantineConsistency.Sign22DegreeStructural

/-! SOURCE-ONLY: finite degree checks for the sign22 seed residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22SyntaxDegree

set_option maxHeartbeats 4000000 in
theorem first_degree_le (p : Fin 4 → ℤ) :
    degree (SharingSeed22Dodecic.firstResidual p) ≤ 6 := by
  change 4 ≤ 6
  decide

set_option maxHeartbeats 4000000 in
theorem remaining_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 23))
    (he : e ∈ SharingSeed22Dodecic.remainingResiduals p) : degree e ≤ 6 := by
  simp only [SharingSeed22Dodecic.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | change 6 ≤ 6
    | change 5 ≤ 6
    | change 4 ≤ 6
    | change 3 ≤ 6
    | change 2 ≤ 6
    | change 1 ≤ 6
    | change 0 ≤ 6
  all_goals decide
end DiophantineConsistency.Sign22SyntaxDegree
#print axioms DiophantineConsistency.Sign22SyntaxDegree.first_degree_le
#print axioms DiophantineConsistency.Sign22SyntaxDegree.remaining_degree_le
