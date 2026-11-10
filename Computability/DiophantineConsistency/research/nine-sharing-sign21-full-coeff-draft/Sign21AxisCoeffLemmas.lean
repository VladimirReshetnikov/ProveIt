import DiophantineConsistency.Sign21AxisResidualDegree
import DiophantineConsistency.Sign21SquareCoeff

/-! SOURCE-ONLY: coefficient consequences of the checked axis degree bounds. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign21LeadingRow
open MvPolynomial

def index14 : Fin 1 →₀ ℕ := Finsupp.single 0 14

theorem index14_sum : ∑ i ∈ index14.support, index14 i = 14 := by
  simp [index14]

theorem square_coeff_zero (e : Expr (Fin 22)) (h : e.weightedDegree weight ≤ 6) :
    coeff index14 (e.evalRing axisPoly * e.evalRing axisPoly) = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  rw [index14_sum]
  have he := axis_poly_degree_le e h
  have hs := MvPolynomial.totalDegree_mul (e.evalRing axisPoly) (e.evalRing axisPoly)
  omega

theorem leading_axis_square_coeff :
    coeff index14 (leading.evalRing axisPoly * leading.evalRing axisPoly) = 1 := by
  simpa only [axisPoly, leading_axis, index14, pow_two] using leading_square_coeff

def axisSquares (rs : List (Expr (Fin 22))) : MvPolynomial (Fin 1) ℤ :=
  (rs.map fun e => e.evalRing axisPoly * e.evalRing axisPoly).sum

theorem remaining_coeff (p : Fin 4 → ℤ) (rs : List (Expr (Fin 22)))
    (h : ∀ e ∈ rs, e ∈ SharingSeed21Degree14.remainingResiduals p) :
    coeff index14 (axisSquares rs) = (rs.count leading : ℤ) := by
  induction rs with
  | nil => simp [axisSquares]
  | cons e es ih =>
    have he : e ∈ SharingSeed21Degree14.remainingResiduals p := h e (by simp)
    have ht : ∀ x ∈ es, x ∈ SharingSeed21Degree14.remainingResiduals p := by
      intro x hx
      exact h x (by simp [hx])
    have hs := ih ht
    change coeff index14 (e.evalRing axisPoly * e.evalRing axisPoly + axisSquares es) = _
    rw [MvPolynomial.coeff_add, hs]
    by_cases hn : e = leading
    · subst e
      simp [leading_axis_square_coeff, add_comm]
    · have hz := square_coeff_zero e (other_weighted_degree_le p e he hn)
      simp [hn, hz]
end DiophantineConsistency.Sign21LeadingRow
#print axioms DiophantineConsistency.Sign21LeadingRow.square_coeff_zero
#print axioms DiophantineConsistency.Sign21LeadingRow.leading_axis_square_coeff
#print axioms DiophantineConsistency.Sign21LeadingRow.remaining_coeff
