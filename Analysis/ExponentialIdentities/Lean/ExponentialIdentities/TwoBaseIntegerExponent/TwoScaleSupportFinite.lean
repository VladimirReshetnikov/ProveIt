import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring

/-!
# Finite two-scale support identities

This module isolates the exact finite algebra behind the ordinary support series

`F(z) = \sum_{a,b >= 0} z^(p^a * q^b)`.

The main theorem is a rectangular inclusion--exclusion identity.  It uses no convergence,
natural-boundary, Mellin-transform, or spectral argument.
-/

namespace LeanProofs.TwoBaseIntegerExponent

open scoped BigOperators

section

variable {R : Type*} [CommRing R]

/-- Rectangular truncation of a two-scale support series. -/
def twoScaleSupportTrunc (p q : ℕ) (z : R) (A B : ℕ) : R :=
  ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B, z ^ (p ^ a * q ^ b)

private theorem twoScaleSupportTrunc_pow_left (p q : ℕ) (z : R) (A B : ℕ) :
    twoScaleSupportTrunc p q (z ^ p) A B =
      ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
        z ^ (p ^ (a + 1) * q ^ b) := by
  simp only [twoScaleSupportTrunc]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← pow_mul]
  congr 1
  rw [pow_succ]
  ring

private theorem twoScaleSupportTrunc_pow_right (p q : ℕ) (z : R) (A B : ℕ) :
    twoScaleSupportTrunc p q (z ^ q) A B =
      ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
        z ^ (p ^ a * q ^ (b + 1)) := by
  simp only [twoScaleSupportTrunc]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← pow_mul]
  congr 1
  rw [pow_succ]
  ring

private theorem twoScaleSupportTrunc_pow_mul (p q : ℕ) (z : R) (A B : ℕ) :
    twoScaleSupportTrunc p q (z ^ (p * q)) A B =
      ∑ a ∈ Finset.range A, ∑ b ∈ Finset.range B,
        z ^ (p ^ (a + 1) * q ^ (b + 1)) := by
  simp only [twoScaleSupportTrunc]
  apply Finset.sum_congr rfl
  intro a ha
  apply Finset.sum_congr rfl
  intro b hb
  rw [← pow_mul]
  congr 1
  rw [pow_succ, pow_succ]
  ring

/-- Exact finite inclusion--exclusion identity behind
`F(z) - F(z^p) - F(z^q) + F(z^(p*q)) = z`.

The asymmetric truncation sizes on the right are the boundary terms for a finite rectangle,
so the theorem has no convergence hypothesis. -/
theorem twoScaleSupportTrunc_succ_succ (p q : ℕ) (z : R) (A B : ℕ) :
    twoScaleSupportTrunc p q z (A + 1) (B + 1) =
      z + twoScaleSupportTrunc p q (z ^ p) A (B + 1) +
        twoScaleSupportTrunc p q (z ^ q) (A + 1) B -
          twoScaleSupportTrunc p q (z ^ (p * q)) A B := by
  rw [twoScaleSupportTrunc_pow_left, twoScaleSupportTrunc_pow_right,
    twoScaleSupportTrunc_pow_mul]
  simp only [twoScaleSupportTrunc, Finset.sum_range_succ', pow_zero, one_mul]
  ring

end

end LeanProofs.TwoBaseIntegerExponent
