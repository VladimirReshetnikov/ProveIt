import FabiusFunction.SecondOrderEulerian
import Mathlib.Combinatorics.Enumerative.Stirling

/-!
# The near-diagonal first-kind numbers and the second-order Eulerian numbers

The `p`-th diagonal of the unsigned first-kind triangle is a fixed nonnegative combination of
binomial coefficients, with the second-order Eulerian numbers as weights:

`c(m+p, m) = ∑_{j ≤ p} ⟪p,j⟫ C(m+p+j, 2p)`   (`stirlingFirst_diagonal`).

The source states this as `c(m, m-p)` with the convention that an out-of-range first-kind
number is zero.  That convention cannot be read off truncated subtraction in `ℕ`: at `m = 0`
and `p ≥ 1` it would give `c(0,0) = 1` on the left and `0` on the right.  Writing the upper
index as `m + p` states exactly the intended range and needs no convention.

The source proves it through the ordinary generating function of the diagonal.  The proof here
is a double induction resting on one termwise binomial identity (`choose_termwise`),

`(j+1) C(N+j, r+1) + (r-j) C(N+j+1, r+1) = N C(N+j, r)`   for `j ≤ r`,

which is Pascal's rule followed by `Nat.choose_succ_right_eq`.  Everything stays in `ℕ`: no
generating function, no subtraction outside the guarded `r - j`, and no rational arithmetic.

The source also records the polynomial continuation `c(x, x-p) = ∑_j ⟪p,j⟫ C(x+j, 2p)`.  Both
sides of that are polynomials in `x` agreeing at every natural number, so it carries no
information beyond the identity proved here; it is not formalized separately because the
corpus has no definition of the continuation of `c` in its upper index.

## Main results

* `choose_termwise`, the termwise binomial identity.
* `sum_secondEulerian_choose_succ`, the induction step in the diagonal index.
* `stirlingFirst_diagonal`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **The termwise identity behind the diagonal formula:** for `j ≤ r`,
`(j+1) C(N+j, r+1) + (r-j) C(N+j+1, r+1) = N C(N+j, r)`.

Both sides vanish when `r` exceeds `N + j`, so no upper bound on `r` is needed. -/
theorem choose_termwise (N j r : ℕ) (hj : j ≤ r) :
    (j + 1) * (N + j).choose (r + 1) + (r - j) * (N + (j + 1)).choose (r + 1) =
      N * (N + j).choose r := by
  rcases le_or_gt r (N + j) with h | h
  · have hp : (N + (j + 1)).choose (r + 1) = (N + j).choose r + (N + j).choose (r + 1) :=
      Nat.choose_succ_succ' (N + j) r
    have hc : (N + j).choose (r + 1) * (r + 1) = (N + j).choose r * (N + j - r) :=
      Nat.choose_succ_right_eq (N + j) r
    have h1 : j + 1 + (r - j) = r + 1 := by omega
    have h2 : N + j - r + (r - j) = N := by omega
    calc (j + 1) * (N + j).choose (r + 1) + (r - j) * (N + (j + 1)).choose (r + 1)
        = (j + 1 + (r - j)) * (N + j).choose (r + 1) + (r - j) * (N + j).choose r := by
          rw [hp]; ring
      _ = (N + j).choose (r + 1) * (r + 1) + (r - j) * (N + j).choose r := by
          rw [h1]; ring
      _ = (N + j).choose r * (N + j - r) + (r - j) * (N + j).choose r := by rw [hc]
      _ = (N + j).choose r * (N + j - r + (r - j)) := by ring
      _ = N * (N + j).choose r := by rw [h2]; ring
  · have e1 : (N + j).choose r = 0 := Nat.choose_eq_zero_of_lt h
    have e2 : (N + j).choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    have e3 : (N + (j + 1)).choose (r + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [e1, e2, e3]
    ring

/-- **The step in the diagonal index:** summing the second-order Eulerian recurrence against
binomial coefficients multiplies the previous diagonal by `N`. -/
theorem sum_secondEulerian_choose_succ (p N : ℕ) :
    ∑ j ∈ range (p + 2), secondEulerian (p + 1) j * (N + j).choose (2 * p + 1) =
      N * ∑ j ∈ range (p + 1), secondEulerian p j * (N + j).choose (2 * p) := by
  have ht : secondEulerian (p + 1) 0 * (N + 0).choose (2 * p + 1)
      = (0 + 1) * secondEulerian p 0 * (N + 0).choose (2 * p + 1) := by
    rw [secondEulerian_zero_right, secondEulerian_zero_right]
  have hS : ∑ i ∈ range (p + 1),
        secondEulerian (p + 1) (i + 1) * (N + (i + 1)).choose (2 * p + 1)
      = ∑ i ∈ range (p + 1),
          ((i + 1 + 1) * secondEulerian p (i + 1) * (N + (i + 1)).choose (2 * p + 1)
            + (2 * p - i) * secondEulerian p i * (N + (i + 1)).choose (2 * p + 1)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [secondEulerian_succ_succ]
    ring
  have hmain : ∑ j ∈ range (p + 2), secondEulerian (p + 1) j * (N + j).choose (2 * p + 1)
      = ∑ j ∈ range (p + 2), (j + 1) * secondEulerian p j * (N + j).choose (2 * p + 1)
        + ∑ i ∈ range (p + 1),
            (2 * p - i) * secondEulerian p i * (N + (i + 1)).choose (2 * p + 1) := by
    rw [Finset.sum_range_succ'
        (fun j => secondEulerian (p + 1) j * (N + j).choose (2 * p + 1)) (p + 1),
      Finset.sum_range_succ'
        (fun j => (j + 1) * secondEulerian p j * (N + j).choose (2 * p + 1)) (p + 1),
      ht, hS, Finset.sum_add_distrib]
    ring
  have hzero : ∑ j ∈ range (p + 2), (j + 1) * secondEulerian p j * (N + j).choose (2 * p + 1)
      = ∑ j ∈ range (p + 1), (j + 1) * secondEulerian p j * (N + j).choose (2 * p + 1) := by
    rw [Finset.sum_range_succ, secondEulerian_succ_self, mul_zero, zero_mul, add_zero]
  rw [hmain, hzero, ← Finset.sum_add_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjp : j ≤ 2 * p := by
    have := Finset.mem_range.mp hj
    omega
  calc (j + 1) * secondEulerian p j * (N + j).choose (2 * p + 1)
        + (2 * p - j) * secondEulerian p j * (N + (j + 1)).choose (2 * p + 1)
      = secondEulerian p j * ((j + 1) * (N + j).choose (2 * p + 1)
          + (2 * p - j) * (N + (j + 1)).choose (2 * p + 1)) := by ring
    _ = secondEulerian p j * (N * (N + j).choose (2 * p)) := by
        rw [choose_termwise N j (2 * p) hjp]
    _ = N * (secondEulerian p j * (N + j).choose (2 * p)) := by ring

/-- **The near-diagonal first-kind numbers:**
`c(m+p, m) = ∑_{j ≤ p} ⟪p,j⟫ C(m+p+j, 2p)`. -/
theorem stirlingFirst_diagonal : ∀ p m : ℕ,
    Nat.stirlingFirst (m + p) m =
      ∑ j ∈ range (p + 1), secondEulerian p j * (m + p + j).choose (2 * p) := by
  intro p
  induction p with
  | zero =>
    intro m
    rw [Nat.add_zero, Nat.stirlingFirst_self, Finset.sum_range_one, secondEulerian_zero_zero,
      Nat.mul_zero, Nat.choose_zero_right, mul_one]
  | succ p ihp =>
    intro m
    induction m with
    | zero =>
      rw [Nat.zero_add, Nat.stirlingFirst_succ_zero]
      symm
      refine Finset.sum_eq_zero fun j hj => ?_
      have hj' : j ≤ p + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
      rcases lt_or_eq_of_le hj' with h | h
      · rw [Nat.choose_eq_zero_of_lt (by omega), mul_zero]
      · rw [h, secondEulerian_eq_zero_of_le (by omega) (le_refl _), zero_mul]
    | succ m ihm =>
      have h1 := ihp (m + 1)
      rw [Nat.add_right_comm m 1 p] at h1
      rw [← Nat.add_assoc] at ihm
      have hR : ∑ j ∈ range (p + 2),
            secondEulerian (p + 1) j * (m + p + 1 + 1 + j).choose (2 * (p + 1))
          = ∑ j ∈ range (p + 2),
              secondEulerian (p + 1) j * (m + p + 1 + j).choose (2 * p + 1)
            + ∑ j ∈ range (p + 2),
              secondEulerian (p + 1) j * (m + p + 1 + j).choose (2 * (p + 1)) := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [show m + p + 1 + 1 + j = m + p + 1 + j + 1 by omega,
          show 2 * (p + 1) = 2 * p + 1 + 1 by omega, Nat.choose_succ_succ']
        ring
      rw [show m + 1 + (p + 1) = m + p + 1 + 1 by omega, Nat.stirlingFirst_succ_succ, h1, ihm, hR,
        sum_secondEulerian_choose_succ]

end Fabius
