import DiophantineConsistency.Sign17DegreeStructural

/-! SOURCE-ONLY: finite degree checks for the sign17 seed residuals. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign17SyntaxDegree

set_option maxHeartbeats 4000000 in
theorem first_degree_le (p : Fin 4 → ℤ) :
    degree (SharingSeed17Degree96.firstResidual p) ≤ 48 := by
  change 22 ≤ 48
  decide

set_option maxHeartbeats 4000000 in
theorem remaining_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 18))
    (he : e ∈ SharingSeed17Degree96.remainingResiduals p) : degree e ≤ 48 := by
  simp only [SharingSeed17Degree96.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | change 48 ≤ 48
    | change 46 ≤ 48
    | change 22 ≤ 48
    | change 7 ≤ 48
    | change 6 ≤ 48
    | change 5 ≤ 48
    | change 2 ≤ 48
  all_goals decide
end DiophantineConsistency.Sign17SyntaxDegree
#print axioms DiophantineConsistency.Sign17SyntaxDegree.first_degree_le
#print axioms DiophantineConsistency.Sign17SyntaxDegree.remaining_degree_le
