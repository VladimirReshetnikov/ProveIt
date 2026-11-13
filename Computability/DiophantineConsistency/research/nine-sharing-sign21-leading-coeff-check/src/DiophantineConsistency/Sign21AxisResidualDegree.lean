import DiophantineConsistency.Sign21LeadingRow

/-! SOURCE-ONLY: weighted degree of sign21 residuals other than the distinguished row. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21LeadingRow
open MvPolynomial

def weight (i : Fin 22) : ℕ := if i = 6 ∨ i = 17 ∨ i = 21 then 1 else 0

set_option maxHeartbeats 4000000 in
theorem first_weighted_degree_le (p : Fin 4 → ℤ) :
    (SharingSeed21Degree14.firstResidual p).weightedDegree weight ≤ 6 := by
  change 0 ≤ 6
  decide

set_option maxHeartbeats 4000000 in
theorem other_weighted_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 22))
    (he : e ∈ SharingSeed21Degree14.remainingResiduals p) (hne : e ≠ leading) :
    e.weightedDegree weight ≤ 6 := by
  simp only [SharingSeed21Degree14.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals
    first
    | exact False.elim (hne rfl)
    | change 6 ≤ 6; decide
    | change 5 ≤ 6; decide
    | change 4 ≤ 6; decide
    | change 3 ≤ 6; decide
    | change 2 ≤ 6; decide
    | change 1 ≤ 6; decide
    | change 0 ≤ 6; decide

def axisPoly : Fin 22 → MvPolynomial (Fin 1) ℤ := axis (X 0)

theorem axisPoly_degree_le (i : Fin 22) : (axisPoly i).totalDegree ≤ weight i := by
  by_cases h0 : i = 0
  · subst i
    simp [axisPoly, axis, weight]
  · by_cases h : i = 6 ∨ i = 17 ∨ i = 21
    · simp [axisPoly, axis, weight, h0, h]
    · simp [axisPoly, axis, weight, h0, h]

theorem axis_poly_degree_le (e : Expr (Fin 22)) (h : e.weightedDegree weight ≤ 6) :
    (e.evalRing axisPoly).totalDegree ≤ 6 :=
  (Expr.degree_evalRing_le e weight axisPoly axisPoly_degree_le).trans h
end DiophantineConsistency.Sign21LeadingRow
#print axioms DiophantineConsistency.Sign21LeadingRow.first_weighted_degree_le
#print axioms DiophantineConsistency.Sign21LeadingRow.other_weighted_degree_le
#print axioms DiophantineConsistency.Sign21LeadingRow.axisPoly_degree_le
#print axioms DiophantineConsistency.Sign21LeadingRow.axis_poly_degree_le
