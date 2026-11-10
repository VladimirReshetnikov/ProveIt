import DiophantineConsistency.Sign20AxisResidualDegree
import DiophantineConsistency.Sign20SquareCoeffs

/-! SOURCE-ONLY: coefficient consequences for the two exceptional rows. -/
set_option autoImplicit false
noncomputable section
namespace DiophantineConsistency.Sign20LeadingRows
open MvPolynomial

def index20 : Fin 1 →₀ ℕ := Finsupp.single 0 20

theorem index20_sum : ∑ i ∈ index20.support, index20 i = 20 := by
  simp [index20]

theorem square_coeff_zero (e : Expr (Fin 21)) (h : e.weightedDegree weight ≤ 6) :
    coeff index20 (e.evalRing axisPoly * e.evalRing axisPoly) = 0 := by
  apply MvPolynomial.coeff_eq_zero_of_totalDegree_lt
  rw [index20_sum]
  have he := axis_poly_degree_le e h
  have hs := MvPolynomial.totalDegree_mul (e.evalRing axisPoly) (e.evalRing axisPoly)
  omega

theorem n0_axis_square_coeff (p : Fin 4 → ℤ) :
    coeff index20 ((n0 p).evalRing axisPoly * (n0 p).evalRing axisPoly) = (p 0)^4 := by
  simpa only [axisPoly, n0_axis, index20, pow_two] using n0_square_coeff (p 0)

theorem dc2_axis_square_coeff (p : Fin 4 → ℤ) :
    coeff index20 ((dc2 p).evalRing axisPoly * (dc2 p).evalRing axisPoly) = (p 0)^4 := by
  simpa only [axisPoly, dc2_axis, index20, pow_two] using dc2_square_coeff (p 0)

theorem rows_distinct (p : Fin 4 → ℤ) : n0 p ≠ dc2 p := by decide

def axisSquares (rs : List (Expr (Fin 21))) : MvPolynomial (Fin 1) ℤ :=
  (rs.map fun e => e.evalRing axisPoly * e.evalRing axisPoly).sum

theorem remaining_coeff (p : Fin 4 → ℤ) (rs : List (Expr (Fin 21)))
    (h : ∀ e ∈ rs, e ∈ SharingSeed20Degree20.remainingResiduals p) :
    coeff index20 (axisSquares rs) = ((rs.count (n0 p) : ℤ) + (rs.count (dc2 p) : ℤ)) * (p 0)^4 := by
  induction rs with
  | nil => simp [axisSquares]
  | cons e es ih =>
    have he : e ∈ SharingSeed20Degree20.remainingResiduals p := h e (by simp)
    have ht : ∀ x ∈ es, x ∈ SharingSeed20Degree20.remainingResiduals p := by
      intro x hx
      exact h x (by simp [hx])
    have hs := ih ht
    change coeff index20 (e.evalRing axisPoly * e.evalRing axisPoly + axisSquares es) = _
    rw [MvPolynomial.coeff_add, hs]
    by_cases hn : e = n0 p
    · subst e
      simp [n0_axis_square_coeff, rows_distinct p, Ne.symm (rows_distinct p), add_assoc, add_comm, add_left_comm] <;> ring
    · by_cases hd : e = dc2 p
      · subst e
        simp [dc2_axis_square_coeff, rows_distinct p, Ne.symm (rows_distinct p), add_assoc, add_comm, add_left_comm] <;> ring
      · have hz := square_coeff_zero e (other_weighted_degree_le p e he hn hd)
        simp [hn, hd, hz]
end DiophantineConsistency.Sign20LeadingRows
#print axioms DiophantineConsistency.Sign20LeadingRows.square_coeff_zero
#print axioms DiophantineConsistency.Sign20LeadingRows.n0_axis_square_coeff
#print axioms DiophantineConsistency.Sign20LeadingRows.dc2_axis_square_coeff
#print axioms DiophantineConsistency.Sign20LeadingRows.rows_distinct
#print axioms DiophantineConsistency.Sign20LeadingRows.remaining_coeff
