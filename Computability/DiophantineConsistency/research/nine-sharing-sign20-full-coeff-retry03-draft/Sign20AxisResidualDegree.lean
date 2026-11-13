import DiophantineConsistency.Sign20LeadingRows

/-! SOURCE-ONLY: weighted degree of sign20 residuals other than N0 and Dc2. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20LeadingRows
open MvPolynomial

def weight (i : Fin 21) : ℕ := if i = 1 ∨ i = 9 ∨ i = 11 ∨ i = 15 then 1 else 0

set_option maxHeartbeats 4000000 in
theorem first_weighted_degree_le (p : Fin 4 → ℤ) :
    (SharingSeed20Degree20.firstResidual p).weightedDegree weight ≤ 6 := by
  change 3 ≤ 6
  decide

set_option maxHeartbeats 4000000 in
theorem other_weighted_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 21))
    (he : e ∈ SharingSeed20Degree20.remainingResiduals p) (hn : e ≠ n0 p) (hd : e ≠ dc2 p) :
    e.weightedDegree weight ≤ 6 := by
  simp only [SharingSeed20Degree20.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals
    first
    | exact False.elim (hn rfl)
    | exact False.elim (hd rfl)
    | change 6 ≤ 6; decide
    | change 5 ≤ 6; decide
    | change 4 ≤ 6; decide
    | change 3 ≤ 6; decide
    | change 2 ≤ 6; decide
    | change 1 ≤ 6; decide
    | change 0 ≤ 6; decide

def axisPoly : Fin 21 → MvPolynomial (Fin 1) ℤ := axis (X 0)

theorem axisPoly_degree_le (i : Fin 21) : (axisPoly i).totalDegree ≤ weight i := by
  by_cases h0 : i = 0
  · subst i
    simp [axisPoly, axis, weight]
  · by_cases h : i = 1 ∨ i = 9 ∨ i = 11 ∨ i = 15
    · simp [axisPoly, axis, weight, h0, h]
    · simp [axisPoly, axis, weight, h0, h]

theorem axis_poly_degree_le (e : Expr (Fin 21)) (h : e.weightedDegree weight ≤ 6) :
    (e.evalRing axisPoly).totalDegree ≤ 6 :=
  (Expr.degree_evalRing_le e weight axisPoly axisPoly_degree_le).trans h
end DiophantineConsistency.Sign20LeadingRows
#print axioms DiophantineConsistency.Sign20LeadingRows.first_weighted_degree_le
#print axioms DiophantineConsistency.Sign20LeadingRows.other_weighted_degree_le
#print axioms DiophantineConsistency.Sign20LeadingRows.axisPoly_degree_le
#print axioms DiophantineConsistency.Sign20LeadingRows.axis_poly_degree_le
