import DiophantineConsistency.Sign23DegreeStructural

/-! SOURCE-ONLY: finite degree checks for the sign24 seed residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23SyntaxDegree

set_option maxHeartbeats 4000000 in
theorem first_degree_le (p : Fin 4 → ℤ) :
    degree (SharingSeed23Octic.firstResidual p) ≤ 4 := by
  change 4 ≤ 4
  decide

set_option maxHeartbeats 4000000 in
theorem remaining_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 24))
    (he : e ∈ SharingSeed23Octic.remainingResiduals p) : degree e ≤ 4 := by
  simp only [SharingSeed23Octic.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | change 4 ≤ 4
    | change 3 ≤ 4
    | change 2 ≤ 4
    | change 1 ≤ 4
    | change 0 ≤ 4
  all_goals decide
end DiophantineConsistency.Sign23SyntaxDegree
#print axioms DiophantineConsistency.Sign23SyntaxDegree.first_degree_le
#print axioms DiophantineConsistency.Sign23SyntaxDegree.remaining_degree_le
