import DiophantineConsistency.Sign21DegreeStructural

/-! SOURCE-ONLY: finite degree checks for the sign21 seed residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21SyntaxDegree

set_option maxHeartbeats 4000000 in
theorem first_degree_le (p : Fin 4 → ℤ) :
    degree (SharingSeed21Degree14.firstResidual p) ≤ 7 := by
  change 4 ≤ 7
  decide

set_option maxHeartbeats 4000000 in
theorem remaining_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 22))
    (he : e ∈ SharingSeed21Degree14.remainingResiduals p) : degree e ≤ 7 := by
  simp only [SharingSeed21Degree14.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals
    first
    | change 7 ≤ 7
    | change 6 ≤ 7
    | change 5 ≤ 7
    | change 4 ≤ 7
    | change 3 ≤ 7
    | change 2 ≤ 7
    | change 1 ≤ 7
    | change 0 ≤ 7
  all_goals decide
end DiophantineConsistency.Sign21SyntaxDegree
#print axioms DiophantineConsistency.Sign21SyntaxDegree.first_degree_le
#print axioms DiophantineConsistency.Sign21SyntaxDegree.remaining_degree_le
