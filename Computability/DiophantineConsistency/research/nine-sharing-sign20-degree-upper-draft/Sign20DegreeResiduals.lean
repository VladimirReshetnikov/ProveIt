import DiophantineConsistency.Sign20DegreeStructural

/-! SOURCE-ONLY: finite degree checks for the sign20 seed residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20SyntaxDegree

set_option maxHeartbeats 4000000 in
theorem first_degree_le (p : Fin 4 → ℤ) :
    degree (SharingSeed20Degree20.firstResidual p) ≤ 10 := by
  change 4 ≤ 10
  decide

set_option maxHeartbeats 4000000 in
theorem remaining_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 21))
    (he : e ∈ SharingSeed20Degree20.remainingResiduals p) : degree e ≤ 10 := by
  simp only [SharingSeed20Degree20.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals
    first
    | change 10 ≤ 10
    | change 9 ≤ 10
    | change 8 ≤ 10
    | change 7 ≤ 10
    | change 6 ≤ 10
    | change 5 ≤ 10
    | change 4 ≤ 10
    | change 3 ≤ 10
    | change 2 ≤ 10
    | change 1 ≤ 10
    | change 0 ≤ 10
  all_goals decide
end DiophantineConsistency.Sign20SyntaxDegree
#print axioms DiophantineConsistency.Sign20SyntaxDegree.first_degree_le
#print axioms DiophantineConsistency.Sign20SyntaxDegree.remaining_degree_le
