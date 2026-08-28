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
* `gaussianBinomial_add_symm` and `gaussianBinomial_symm` prove
  complementary-index symmetry without division or cancellation.
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

/-- **Degree-indexed principal specialization.**  On the `p + 1` variables
`1, q, ..., q^p`, the degree-`r` complete homogeneous polynomial is the
denominator-free Gaussian coefficient `[p+r choose r]_q`.

This is the orientation in which the lower Gaussian index records the
homogeneous degree.  Its direct adjoining-variable proof is the dual of
`completeHomogeneousEval_geometric`; comparing the two orientations below
will expose Gaussian symmetry without division or cancellation. -/
theorem completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial_degree
    {R : Type*} [CommSemiring R]
    (q : R) (p r : ℕ) :
    completeHomogeneousEvalOn (Finset.range (p + 1))
        (fun j : ℕ ↦ q ^ j) r =
      gaussianBinomial q (p + r) r := by
  induction p generalizing r with
  | zero =>
      simpa using
        (completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial q 0 r)
  | succ p ih =>
      induction r with
      | zero =>
          simpa using
            (completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial q (p + 1) 0)
      | succ r ihr =>
          have hrange :
              insert (p + 1) (Finset.range (p + 1)) =
                Finset.range ((p + 1) + 1) :=
            (Finset.range_add_one (n := p + 1)).symm
          have hrec := completeHomogeneousEvalOn_insert_succ
            (s := Finset.range (p + 1)) (i := p + 1)
            Finset.notMem_range_self
            (fun j : ℕ ↦ q ^ j) r
          rw [hrange] at hrec
          rw [show Nat.succ p + 1 = (p + 1) + 1 by omega,
            hrec, ihr, ih (r + 1)]
          have hinner : Nat.succ p + r = p + r + 1 := by omega
          have houter : p + (r + 1) = p + r + 1 := by omega
          have hgoal :
              Nat.succ p + (r + 1) = (p + r + 1) + 1 := by omega
          have hexponent : p + r + 1 - r = p + 1 := by omega
          rw [hinner, houter, hgoal]
          simpa only [hexponent, add_comm] using
            (gaussianBinomial_succ_succ q (p + r + 1) r).symm

/-- Complementary-index symmetry in an additively parameterized Gaussian
row.  The identity holds over every commutative semiring, including at
singular values of `q`, because it compares two denominator-free principal
specializations of the same complete homogeneous polynomial. -/
theorem gaussianBinomial_add_symm
    {R : Type*} [CommSemiring R]
    (q : R) (p r : ℕ) :
    gaussianBinomial q (p + r) p =
      gaussianBinomial q (p + r) r := by
  calc
    gaussianBinomial q (p + r) p =
        gaussianBinomial q (r + p) p := by
      rw [Nat.add_comm p r]
    _ = completeHomogeneousEvalOn (Finset.range (p + 1))
          (fun j : ℕ ↦ q ^ j) r :=
      (completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial
        q p r).symm
    _ = gaussianBinomial q (p + r) r :=
      completeHomogeneousEvalOn_range_pow_eq_gaussianBinomial_degree
        q p r

/-- Reflection `k ↦ n - k` for denominator-free Gaussian coefficients.
No theorem about quotients is used, so symmetry remains valid when a finite
q-Pochhammer denominator vanishes. -/
theorem gaussianBinomial_symm
    {R : Type*} [CommSemiring R]
    (q : R) {n k : ℕ} (hk : k ≤ n) :
    gaussianBinomial q n (n - k) =
      gaussianBinomial q n k := by
  have hsymm := gaussianBinomial_add_symm q k (n - k)
  rw [Nat.add_sub_of_le hk] at hsymm
  exact hsymm.symm

end

end Fabius
