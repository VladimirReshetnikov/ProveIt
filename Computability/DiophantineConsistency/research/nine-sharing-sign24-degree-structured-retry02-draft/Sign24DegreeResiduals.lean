import DiophantineConsistency.Sign24DegreeStructural

/-! SOURCE-ONLY: finite degree checks for the sign24 seed residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24SyntaxDegree

set_option maxHeartbeats 4000000 in
theorem first_degree_le (p : Fin 4 → ℤ) :
    degree (SharingSeed24Octic.firstResidual p) ≤ 4 := by
  change 4 ≤ 4
  decide

set_option maxHeartbeats 4000000 in
theorem remaining_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 25))
    (he : e ∈ SharingSeed24Octic.remainingResiduals p) : degree e ≤ 4 := by
  simp only [SharingSeed24Octic.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | change 4 ≤ 4
    | change 3 ≤ 4
    | change 2 ≤ 4
    | change 1 ≤ 4
    | change 0 ≤ 4
  all_goals decide
end DiophantineConsistency.Sign24SyntaxDegree
#print axioms DiophantineConsistency.Sign24SyntaxDegree.first_degree_le
#print axioms DiophantineConsistency.Sign24SyntaxDegree.remaining_degree_le
