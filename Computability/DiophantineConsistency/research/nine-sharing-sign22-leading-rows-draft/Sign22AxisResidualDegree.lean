import DiophantineConsistency.Sign22LeadingRows

/-! SOURCE-ONLY: weighted degree of sign22 residuals other than N0 and Dc2. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22LeadingRows
open MvPolynomial

def weight (i : Fin 23) : ℕ := if i = 11 ∨ i = 12 ∨ i = 15 ∨ i = 16 then 1 else 0

set_option maxHeartbeats 4000000 in
theorem first_weighted_degree_le (p : Fin 4 → ℤ) :
    (SharingSeed22Dodecic.firstResidual p).weightedDegree weight ≤ 4 := by
  change 1 ≤ 4
  decide

set_option maxHeartbeats 4000000 in
theorem other_weighted_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 23))
    (he : e ∈ SharingSeed22Dodecic.remainingResiduals p) (hn : e ≠ n0) (hd : e ≠ dc2) :
    e.weightedDegree weight ≤ 4 := by
  simp only [SharingSeed22Dodecic.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact False.elim (hn rfl)
    | exact False.elim (hd rfl)
    | change 4 ≤ 4; decide
    | change 3 ≤ 4; decide
    | change 2 ≤ 4; decide
    | change 1 ≤ 4; decide
    | change 0 ≤ 4; decide

def axisPoly : Fin 23 → MvPolynomial (Fin 1) ℤ := axis (X 0)

theorem axisPoly_degree_le (i : Fin 23) : (axisPoly i).totalDegree ≤ weight i := by
  by_cases h0 : i = 0
  · subst i
    simp [axisPoly, axis, weight]
  · by_cases h : i = 11 ∨ i = 12 ∨ i = 15 ∨ i = 16
    · simp [axisPoly, axis, weight, h0, h]
    · simp [axisPoly, axis, weight, h0, h]

theorem axis_poly_degree_le (e : Expr (Fin 23)) (h : e.weightedDegree weight ≤ 4) :
    (e.evalRing axisPoly).totalDegree ≤ 4 :=
  (Expr.degree_evalRing_le e weight axisPoly axisPoly_degree_le).trans h
end DiophantineConsistency.Sign22LeadingRows
#print axioms DiophantineConsistency.Sign22LeadingRows.first_weighted_degree_le
#print axioms DiophantineConsistency.Sign22LeadingRows.other_weighted_degree_le
#print axioms DiophantineConsistency.Sign22LeadingRows.axisPoly_degree_le
#print axioms DiophantineConsistency.Sign22LeadingRows.axis_poly_degree_le
