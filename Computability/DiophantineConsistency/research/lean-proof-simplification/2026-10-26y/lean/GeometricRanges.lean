import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Int
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace ProofSimplificationNew
open Finset
open scoped BigOperators

theorem geometric_identity (B : ℤ) (d : ℕ) :
    (B - 1) * (∑ i ∈ range d, B ^ i) = B ^ d - 1 :=
  mul_geom_sum B d

theorem geometric_lt_two_top {B : ℤ} (hB : 2 ≤ B) (d : ℕ) :
    (∑ i ∈ range (d + 1), B ^ i) < 2 * B ^ d := by
  rw [sum_range_succ]
  have hs : 0 ≤ ∑ i ∈ range d, B ^ i :=
    sum_nonneg (fun i _ => pow_nonneg (by omega : 0 ≤ B) i)
  nlinarith [mul_geom_sum B d, mul_nonneg (show 0 ≤ B - 2 by omega) hs]

#print axioms geometric_identity
#print axioms geometric_lt_two_top
end ProofSimplificationNew
