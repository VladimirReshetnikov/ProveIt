import DiophantineConsistency.Sign24LeadingN0

/-! SOURCE-ONLY: weighted degree of sign24 residuals other than N0. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24LeadingN0
open MvPolynomial

def weight (i : Fin 25) : ℕ := if i = 16 ∨ i = 17 then 1 else 0

set_option maxHeartbeats 4000000 in
theorem first_weighted_degree_le (p : Fin 4 → ℤ) :
    (SharingSeed24Octic.firstResidual p).weightedDegree weight ≤ 2 := by
  change 0 ≤ 2
  decide

set_option maxHeartbeats 4000000 in
theorem other_weighted_degree_le (p : Fin 4 → ℤ) (e : Expr (Fin 25))
    (he : e ∈ SharingSeed24Octic.remainingResiduals p) (hne : e ≠ n0) :
    e.weightedDegree weight ≤ 2 := by
  simp only [SharingSeed24Octic.remainingResiduals, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    first
    | exact False.elim (hne rfl)
    | change 2 ≤ 2; decide
    | change 1 ≤ 2; decide
    | change 0 ≤ 2; decide

def axisPoly : Fin 25 → MvPolynomial (Fin 1) ℤ := axis (X 0)

theorem axisPoly_degree_le (i : Fin 25) : (axisPoly i).totalDegree ≤ weight i := by
  by_cases h0 : i = 0
  · subst i
    simp [axisPoly, axis, weight]
  · by_cases h : i = 16 ∨ i = 17
    · simp [axisPoly, axis, weight, h0, h]
    · simp [axisPoly, axis, weight, h0, h]

theorem axis_poly_degree_le (e : Expr (Fin 25)) (h : e.weightedDegree weight ≤ 2) :
    (e.evalRing axisPoly).totalDegree ≤ 2 :=
  (Expr.degree_evalRing_le e weight axisPoly axisPoly_degree_le).trans h
end DiophantineConsistency.Sign24LeadingN0
#print axioms DiophantineConsistency.Sign24LeadingN0.first_weighted_degree_le
#print axioms DiophantineConsistency.Sign24LeadingN0.other_weighted_degree_le
#print axioms DiophantineConsistency.Sign24LeadingN0.axisPoly_degree_le
#print axioms DiophantineConsistency.Sign24LeadingN0.axis_poly_degree_le
