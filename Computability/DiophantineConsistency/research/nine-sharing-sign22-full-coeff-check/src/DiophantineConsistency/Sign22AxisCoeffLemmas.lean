import DiophantineConsistency.Sign22AxisResidualDegree
import DiophantineConsistency.Sign22SquareCoeffs

/-! SOURCE-ONLY: coefficient consequences for the two exceptional rows. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign22LeadingRows
open MvPolynomial

def index12 : Fin 1 →₀ ℕ := Finsupp.single 0 12

theorem index12_sum : ∑ i ∈ index12.support, index12 i = 12 := by
  simp [index12]

theorem square_coeff_zero (e : Expr (Fin 23)) (h : e.weightedDegree weight ≤ 4) :
    coeff index12 (e.evalRing axisPoly * e.evalRing axisPoly) = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  rw [index12_sum]
  have he := axis_poly_degree_le e h
  have hs := MvPolynomial.totalDegree_mul (e.evalRing axisPoly) (e.evalRing axisPoly)
  omega

theorem n0_axis_square_coeff :
    coeff index12 (n0.evalRing axisPoly * n0.evalRing axisPoly) = 16 := by
  simpa only [axisPoly, n0_axis, index12, pow_two] using n0_square_coeff

theorem dc2_axis_square_coeff :
    coeff index12 (dc2.evalRing axisPoly * dc2.evalRing axisPoly) = 256 := by
  simpa only [axisPoly, dc2_axis, index12, pow_two] using dc2_square_coeff

theorem rows_distinct : n0 ≠ dc2 := by decide

def axisSquares (rs : List (Expr (Fin 23))) : MvPolynomial (Fin 1) ℤ :=
  (rs.map fun e => e.evalRing axisPoly * e.evalRing axisPoly).sum

theorem remaining_coeff (p : Fin 4 → ℤ) (rs : List (Expr (Fin 23)))
    (h : ∀ e ∈ rs, e ∈ SharingSeed22Dodecic.remainingResiduals p) :
    coeff index12 (axisSquares rs) = 16 * (rs.count n0 : ℤ) + 256 * (rs.count dc2 : ℤ) := by
  induction rs with
  | nil => simp [axisSquares]
  | cons e es ih =>
    have he : e ∈ SharingSeed22Dodecic.remainingResiduals p := h e (by simp)
    have ht : ∀ x ∈ es, x ∈ SharingSeed22Dodecic.remainingResiduals p := by
      intro x hx
      exact h x (by simp [hx])
    have hs := ih ht
    change coeff index12 (e.evalRing axisPoly * e.evalRing axisPoly + axisSquares es) = _
    rw [MvPolynomial.coeff_add, hs]
    by_cases hn : e = n0
    · subst e
      simp [n0_axis_square_coeff, rows_distinct, Ne.symm rows_distinct, add_assoc, add_comm, add_left_comm] <;> ring
    · by_cases hd : e = dc2
      · subst e
        simp [dc2_axis_square_coeff, rows_distinct, Ne.symm rows_distinct, add_assoc, add_comm, add_left_comm] <;> ring
      · have hz := square_coeff_zero e (other_weighted_degree_le p e he hn hd)
        simp [hn, hd, hz]
end DiophantineConsistency.Sign22LeadingRows
#print axioms DiophantineConsistency.Sign22LeadingRows.square_coeff_zero
#print axioms DiophantineConsistency.Sign22LeadingRows.n0_axis_square_coeff
#print axioms DiophantineConsistency.Sign22LeadingRows.dc2_axis_square_coeff
#print axioms DiophantineConsistency.Sign22LeadingRows.rows_distinct
#print axioms DiophantineConsistency.Sign22LeadingRows.remaining_coeff
