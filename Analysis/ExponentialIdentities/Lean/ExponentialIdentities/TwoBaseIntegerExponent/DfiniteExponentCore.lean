import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.RingTheory.Algebraic.Basic
import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Tactic

/-!
# The algebraic core of the D-finite power-germ criterion

For a differential operator

`L = ∑ j, p j * d^j/dz^j`

of order `r`, applying `L` to the formal power `z^λ` and multiplying by
`z^(r-λ)` produces the bivariate polynomial

`Q(z, λ) = ∑ j ≤ r, p j(z) * (λ)_j * z^(r-j)`.

Here `(λ)_j` is the descending Pochhammer polynomial.  This file isolates
the key noncancellation in report 27: the coefficient of `λ^r` in `Q` is
exactly the leading differential coefficient `p r`.  In particular, a genuine
order-`r` operator produces a nonzero algebraic relation polynomial.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open Finset Polynomial

namespace DfiniteExponentCore

variable {K : Type*} [Field K]

/-- The bivariate polynomial attached to an order-`r` differential operator.
The outer polynomial variable is the exponent and the inner variable is `z`. -/
noncomputable def exponentRelationPolynomial
    (r : ℕ) (p : ℕ → K[X]) : K[X][X] :=
  ∑ j ∈ range (r + 1),
    C (p j * X ^ (r - j)) * descPochhammer K[X] j

/-- The top exponent coefficient cannot cancel: it is precisely the leading
coefficient polynomial of the differential operator. -/
theorem coeff_exponentRelationPolynomial_order
    (r : ℕ) (p : ℕ → K[X]) :
    (exponentRelationPolynomial r p).coeff r = p r := by
  classical
  rw [exponentRelationPolynomial, finsetSum_coeff]
  simp only [coeff_C_mul]
  rw [Finset.sum_eq_single r]
  · have htop : (descPochhammer K[X] r).coeff r = 1 := by
      simpa using (monic_descPochhammer K[X] r).coeff_natDegree
    simp [htop]
  · intro j hj hjr
    have hjle : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hjlt : j < r := lt_of_le_of_ne hjle hjr
    have hdeg : (descPochhammer K[X] j).natDegree < r := by
      simpa using hjlt
    simp [coeff_eq_zero_of_natDegree_lt hdeg]
  · simp

/-- A nonzero leading differential coefficient makes the bivariate exponent
relation polynomial nonzero. -/
theorem exponentRelationPolynomial_ne_zero
    (r : ℕ) (p : ℕ → K[X]) (hp : p r ≠ 0) :
    exponentRelationPolynomial r p ≠ 0 := by
  intro hzero
  have hcoeff : (exponentRelationPolynomial r p).coeff r = 0 := by
    rw [hzero]
    simp
  rw [coeff_exponentRelationPolynomial_order] at hcoeff
  exact hp hcoeff

end DfiniteExponentCore

end LeanProofs.TwoBaseIntegerExponent
