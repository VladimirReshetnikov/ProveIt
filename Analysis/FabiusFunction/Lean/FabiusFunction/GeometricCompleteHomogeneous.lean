import FabiusFunction.CompleteHomogeneous
import FabiusFunction.FiniteQBinomialCore

/-!
# Principal specialization of complete homogeneous polynomials

This module identifies the complete homogeneous symmetric polynomial on a
finite geometric alphabet with the denominator-free Gaussian coefficient:

`h_n(1, q, ..., q^r) = gaussianBinomial q (n + r) r`.

The identity is proved over an arbitrary commutative semiring.  In
particular it remains valid at `q = 0`, at roots of unity, in positive
characteristic, and in the zero semiring.  There is no quotient and no
distinctness, nonzeroness, ordering, or topology hypothesis.

The proof mirrors the symmetric-function structure.  Splitting off the
leading variable `1` leaves a tail obtained by scaling
`(1, q, ..., q^(r-1))` by `q`; homogeneity then turns the head--tail
recurrence into q-Pascal's recurrence.

## Main results

* `completeHomogeneousEval_geometric` is the principal specialization.
* `completeHomogeneousEval_scaled_geometric` allows an arbitrary common
  scale on the geometric alphabet.
* `completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial` gives the same
  result in the `Finset.range` representation used by interpolation rows.
-/

set_option autoImplicit false

namespace Fabius

noncomputable section

/-- **Principal specialization of complete homogeneous polynomials.**

For every commutative semiring,
`h_n(1, q, ..., q^r) = gaussianBinomial q (n + r) r`.
The recursive Gaussian coefficient makes the statement meaningful without
division at every value of `q`. -/
theorem completeHomogeneousEval_geometric
    {R : Type*} [CommSemiring R]
    (q : R) (n r : ℕ) :
    completeHomogeneousEval
        (fun j : Fin (r + 1) ↦ q ^ (j : ℕ)) n =
      gaussianBinomial q (n + r) r := by
  induction n generalizing r with
  | zero => simp
  | succ n ih =>
      induction r with
      | zero =>
          rw [completeHomogeneousEval_fin_succ]
          simp only [Fin.val_zero, pow_zero, one_mul,
            completeHomogeneousEval_isEmpty_succ]
          rw [ih]
          simp
      | succ r ihr =>
          rw [completeHomogeneousEval_fin_succ]
          simp only [Fin.val_zero, pow_zero, one_mul]
          have htail :
              completeHomogeneousEval
                  (fun j : Fin (r + 1) ↦ q ^ (j.succ : ℕ)) (n + 1) =
                q ^ (n + 1) * gaussianBinomial q (n + 1 + r) r := by
            calc
              completeHomogeneousEval
                    (fun j : Fin (r + 1) ↦ q ^ (j.succ : ℕ)) (n + 1) =
                  completeHomogeneousEval
                    (fun j : Fin (r + 1) ↦ q * q ^ (j : ℕ)) (n + 1) := by
                congr 1
                funext j
                change q ^ ((j : ℕ) + 1) = q * q ^ (j : ℕ)
                rw [pow_succ']
              _ = q ^ (n + 1) * completeHomogeneousEval
                    (fun j : Fin (r + 1) ↦ q ^ (j : ℕ)) (n + 1) :=
                completeHomogeneousEval_smul q
                  (fun j : Fin (r + 1) ↦ q ^ (j : ℕ)) (n + 1)
              _ = q ^ (n + 1) * gaussianBinomial q (n + 1 + r) r := by
                rw [ihr]
          rw [htail, ih (r + 1)]
          have hleft : n + (r + 1) = n + r + 1 := by omega
          have hright : n + 1 + r = n + r + 1 := by omega
          have htotal : n + 1 + (r + 1) = (n + r + 1) + 1 := by omega
          rw [hleft, hright, htotal]
          have hexp : n + r + 1 - r = n + 1 := by omega
          simpa only [hexp, add_comm] using
            (gaussianBinomial_succ_succ q (n + r + 1) r).symm

/-- A common scale `c` contributes the homogeneous factor `c ^ n` to the
geometric principal specialization.  The scale may be zero or a zero
divisor. -/
theorem completeHomogeneousEval_scaled_geometric
    {R : Type*} [CommSemiring R]
    (c q : R) (n r : ℕ) :
    completeHomogeneousEval
        (fun j : Fin (r + 1) ↦ c * q ^ (j : ℕ)) n =
      c ^ n * gaussianBinomial q (n + r) r := by
  rw [completeHomogeneousEval_smul,
    completeHomogeneousEval_geometric]

/-- Range-indexed form of the geometric principal specialization. -/
theorem completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial
    {R : Type*} [CommSemiring R]
    (q : R) (p n : ℕ) :
    completeHomogeneousEvalOn (Finset.range (p + 1))
        (fun k : ℕ ↦ q ^ k) n =
      gaussianBinomial q (n + p) p := by
  rw [completeHomogeneousEvalOn_range]
  exact completeHomogeneousEval_geometric q n p

end

end Fabius
