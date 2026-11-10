import DiophantineConsistency.Sign24AxisResidualDegree
import DiophantineConsistency.Sign24N0SquareCoeff

/-! SOURCE-ONLY: coefficient consequences of the checked axis degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign24LeadingN0
open MvPolynomial

def index8 : Fin 1 →₀ ℕ := Finsupp.single 0 8

theorem index8_sum : ∑ i ∈ index8.support, index8 i = 8 := by
  simp [index8]

theorem square_coeff_zero (e : Expr (Fin 25)) (h : e.weightedDegree weight ≤ 2) :
    coeff index8 (e.evalRing axisPoly * e.evalRing axisPoly) = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  rw [index8_sum]
  have he := axis_poly_degree_le e h
  have hs := MvPolynomial.totalDegree_mul (e.evalRing axisPoly) (e.evalRing axisPoly)
  omega

theorem n0_axis_square_coeff :
    coeff index8 (n0.evalRing axisPoly * n0.evalRing axisPoly) = 1 := by
  simpa only [axisPoly, n0_axis, index8, pow_two] using n0_square_coeff

def axisSquares (rs : List (Expr (Fin 25))) : MvPolynomial (Fin 1) ℤ :=
  (rs.map fun e => e.evalRing axisPoly * e.evalRing axisPoly).sum

theorem remaining_coeff (p : Fin 4 → ℤ) (rs : List (Expr (Fin 25)))
    (h : ∀ e ∈ rs, e ∈ SharingSeed24Octic.remainingResiduals p) :
    coeff index8 (axisSquares rs) = (rs.count n0 : ℤ) := by
  induction rs with
  | nil => simp [axisSquares]
  | cons e es ih =>
    have he : e ∈ SharingSeed24Octic.remainingResiduals p := h e (by simp)
    have ht : ∀ x ∈ es, x ∈ SharingSeed24Octic.remainingResiduals p := by
      intro x hx
      exact h x (by simp [hx])
    have hs := ih ht
    change coeff index8 (e.evalRing axisPoly * e.evalRing axisPoly + axisSquares es) = _
    rw [MvPolynomial.coeff_add, hs]
    by_cases hn : e = n0
    · subst e
      simp [List.count_cons, n0_axis_square_coeff]
    · have hz := square_coeff_zero e (other_weighted_degree_le p e he hn)
      simp [List.count_cons, hn, hz]
end DiophantineConsistency.Sign24LeadingN0
#print axioms DiophantineConsistency.Sign24LeadingN0.square_coeff_zero
#print axioms DiophantineConsistency.Sign24LeadingN0.n0_axis_square_coeff
#print axioms DiophantineConsistency.Sign24LeadingN0.remaining_coeff
