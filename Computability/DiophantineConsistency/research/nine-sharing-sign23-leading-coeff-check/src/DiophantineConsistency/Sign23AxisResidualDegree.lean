import DiophantineConsistency.Sign23LeadingRows

/-! SOURCE-ONLY: weighted degree of sign23 residuals other than N0 and Dc2. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23LeadingRows
open MvPolynomial

def weight (i : Fin 24) : ℕ := if i = 16 ∨ i = 17 then 1 else 0

set_option maxHeartbeats 4000000 in
theorem first_weighted_degree_le (p : Fin 4 → ℤ) :
    (SharingSeed23Octic.firstResidual p).weightedDegree weight ≤ 2 := by
  change 0 ≤ 2
  decide

set_option maxHeartbeats 4000000 in
theorem other_weighted_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 24))
    (he : e ∈ SharingSeed23Octic.remainingResiduals p) (hn : e ≠ n0) (hd : e ≠ dc2) :
    e.weightedDegree weight ≤ 2 := by
  simp only [SharingSeed23Octic.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact False.elim (hn rfl)
    | exact False.elim (hd rfl)
    | change 2 ≤ 2; decide
    | change 1 ≤ 2; decide
    | change 0 ≤ 2; decide

def axisPoly : Fin 24 → MvPolynomial (Fin 1) ℤ := axis (X 0)

theorem axisPoly_degree_le (i : Fin 24) : (axisPoly i).totalDegree ≤ weight i := by
  by_cases h0 : i = 0
  · subst i
    simp [axisPoly, axis, weight]
  · by_cases h : i = 16 ∨ i = 17
    · simp [axisPoly, axis, weight, h0, h]
    · simp [axisPoly, axis, weight, h0, h]

theorem axis_poly_degree_le (e : Expr (Fin 24)) (h : e.weightedDegree weight ≤ 2) :
    (e.evalRing axisPoly).totalDegree ≤ 2 :=
  (Expr.degree_evalRing_le e weight axisPoly axisPoly_degree_le).trans h
end DiophantineConsistency.Sign23LeadingRows
#print axioms DiophantineConsistency.Sign23LeadingRows.first_weighted_degree_le
#print axioms DiophantineConsistency.Sign23LeadingRows.other_weighted_degree_le
#print axioms DiophantineConsistency.Sign23LeadingRows.axisPoly_degree_le
#print axioms DiophantineConsistency.Sign23LeadingRows.axis_poly_degree_le
