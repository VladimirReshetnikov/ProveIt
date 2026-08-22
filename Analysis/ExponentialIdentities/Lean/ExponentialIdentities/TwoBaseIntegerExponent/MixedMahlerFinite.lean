import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite mixed Mahler identities

This file isolates the exact finite algebra behind the mixed `(2,3)`-Mahler series

`H(z) = \sum_{a,b >= 0} M^a N^b z^(2^a 3^b)`.

No convergence, analytic continuation, or natural-boundary theorem is used here.  The main
identity is a rectangular finite-sum inclusion--exclusion formula; the usual infinite Mahler
equation follows from it once a separate limiting argument is supplied.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators

section

variable {R : Type*} [CommRing R]

/-- Rectangular truncation of the mixed `(2,3)`-Mahler series. -/
def mixedMahlerTrunc (M N z : R) (A B : ℕ) : R :=
  ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
    M ^ a * N ^ b * z ^ (2 ^ a * 3 ^ b)

private theorem mul_mixedMahlerTrunc_sq (M N z : R) (A B : ℕ) :
    M * mixedMahlerTrunc M N (z ^ 2) A B =
      ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
        M ^ (a + 1) * N ^ b * z ^ (2 ^ (a + 1) * 3 ^ b) := by
  simp only [mixedMahlerTrunc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← pow_mul]
  have hexp : 2 * (2 ^ a * 3 ^ b) = 2 ^ (a + 1) * 3 ^ b := by
    rw [pow_succ]
    ring
  rw [hexp, pow_succ]
  ring

private theorem mul_mixedMahlerTrunc_cube (M N z : R) (A B : ℕ) :
    N * mixedMahlerTrunc M N (z ^ 3) A B =
      ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
        M ^ a * N ^ (b + 1) * z ^ (2 ^ a * 3 ^ (b + 1)) := by
  simp only [mixedMahlerTrunc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← pow_mul]
  have hexp : 3 * (2 ^ a * 3 ^ b) = 2 ^ a * 3 ^ (b + 1) := by
    rw [pow_succ]
    ring
  rw [hexp, pow_succ]
  ring

private theorem mul_mixedMahlerTrunc_six (M N z : R) (A B : ℕ) :
    (M * N) * mixedMahlerTrunc M N (z ^ 6) A B =
      ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
        M ^ (a + 1) * N ^ (b + 1) *
          z ^ (2 ^ (a + 1) * 3 ^ (b + 1)) := by
  simp only [mixedMahlerTrunc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← pow_mul]
  have hexp : 6 * (2 ^ a * 3 ^ b) = 2 ^ (a + 1) * 3 ^ (b + 1) := by
    rw [pow_succ, pow_succ]
    ring
  rw [hexp, pow_succ, pow_succ]
  ring

/-- Exact finite inclusion--exclusion identity behind
`H(z) = z + M H(z^2) + N H(z^3) - MN H(z^6)`.

The asymmetric truncation sizes on the right are the exact boundary terms needed for a
rectangular finite sum, so the statement has no convergence hypothesis. -/
theorem mixedMahlerTrunc_succ_succ (M N z : R) (A B : ℕ) :
    mixedMahlerTrunc M N z (A + 1) (B + 1) =
      z + M * mixedMahlerTrunc M N (z ^ 2) A (B + 1) +
        N * mixedMahlerTrunc M N (z ^ 3) (A + 1) B -
          (M * N) * mixedMahlerTrunc M N (z ^ 6) A B := by
  rw [mul_mixedMahlerTrunc_sq, mul_mixedMahlerTrunc_cube,
    mul_mixedMahlerTrunc_six]
  simp only [mixedMahlerTrunc, Finset.sum_range_succ', pow_zero, one_mul]
  ring

end


end LeanProofs.TwoBaseIntegerExponent
