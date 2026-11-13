import DiophantineConsistency.Sign23AxisResidualDegree
import DiophantineConsistency.Sign23SquareCoeffs

/-! SOURCE-ONLY: coefficient consequences for the two exceptional rows. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign23LeadingRows
open MvPolynomial

def index8 : Fin 1 →₀ ℕ := Finsupp.single 0 8

theorem index8_sum : ∑ i ∈ index8.support, index8 i = 8 := by
  simp [index8]

theorem square_coeff_zero (e : Expr (Fin 24)) (h : e.weightedDegree weight ≤ 2) :
    coeff index8 (e.evalRing axisPoly * e.evalRing axisPoly) = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  rw [index8_sum]
  have he := axis_poly_degree_le e h
  have hs := MvPolynomial.totalDegree_mul (e.evalRing axisPoly) (e.evalRing axisPoly)
  omega

theorem n0_axis_square_coeff :
    coeff index8 (n0.evalRing axisPoly * n0.evalRing axisPoly) = 1 := by
  simpa only [axisPoly, n0_axis, index8, pow_two] using n0_square_coeff

theorem dc2_axis_square_coeff :
    coeff index8 (dc2.evalRing axisPoly * dc2.evalRing axisPoly) = 1 := by
  simpa only [axisPoly, dc2_axis, index8, pow_two] using dc2_square_coeff

theorem rows_distinct : n0 ≠ dc2 := by decide

def axisSquares (rs : List (Expr (Fin 24))) : MvPolynomial (Fin 1) ℤ :=
  (rs.map fun e => e.evalRing axisPoly * e.evalRing axisPoly).sum

theorem remaining_coeff (p : Fin 4 → ℤ) (rs : List (Expr (Fin 24)))
    (h : ∀ e ∈ rs, e ∈ SharingSeed23Octic.remainingResiduals p) :
    coeff index8 (axisSquares rs) = (rs.count n0 : ℤ) + (rs.count dc2 : ℤ) := by
  induction rs with
  | nil => simp [axisSquares]
  | cons e es ih =>
    have he : e ∈ SharingSeed23Octic.remainingResiduals p := h e (by simp)
    have ht : ∀ x ∈ es, x ∈ SharingSeed23Octic.remainingResiduals p := by
      intro x hx
      exact h x (by simp [hx])
    have hs := ih ht
    change coeff index8 (e.evalRing axisPoly * e.evalRing axisPoly + axisSquares es) = _
    rw [MvPolynomial.coeff_add, hs]
    by_cases hn : e = n0
    · subst e
      simp [n0_axis_square_coeff, rows_distinct, Ne.symm rows_distinct, add_assoc, add_comm, add_left_comm]
    · by_cases hd : e = dc2
      · subst e
        simp [dc2_axis_square_coeff, rows_distinct, Ne.symm rows_distinct, add_assoc, add_comm, add_left_comm]
      · have hz := square_coeff_zero e (other_weighted_degree_le p e he hn hd)
        simp [hn, hd, hz]
end DiophantineConsistency.Sign23LeadingRows
#print axioms DiophantineConsistency.Sign23LeadingRows.square_coeff_zero
#print axioms DiophantineConsistency.Sign23LeadingRows.n0_axis_square_coeff
#print axioms DiophantineConsistency.Sign23LeadingRows.dc2_axis_square_coeff
#print axioms DiophantineConsistency.Sign23LeadingRows.rows_distinct
#print axioms DiophantineConsistency.Sign23LeadingRows.remaining_coeff
