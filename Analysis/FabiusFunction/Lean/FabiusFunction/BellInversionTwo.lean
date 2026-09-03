import FabiusFunction.BellShiftEGF

/-!
# The two-sided Bell inversion identity

The source's second Bell inversion identity is

`∑_{j ≤ n} C(n,j) B(k+j) = ∑_{i ≤ k} (-1)^{k-i} C(k,i) B(n+i+1)`
(`sum_choose_bell_add_eq_sum_neg_one_pow`).

The source proves it probabilistically, through the moments of a Poisson variable of mean one
and a summation-by-parts identity for that variable.  Neither ingredient is available here,
and neither is needed: both sides satisfy the same recurrence in `k`,

`H(n, k+1) = H(n+1, k) - H(n, k)`,

and agree at `k = 0`, where both are `B(n+1)` by the Bell recurrence.  Each recurrence is
Pascal's rule plus a shift of the summation index, so the whole proof is a double induction in
`ℤ` with no probability and no generating function.

The two sides are given names (`bellForward`, `bellBackward`) rather than being manipulated
inline, because the recurrence is a statement about them as functions of two arguments and the
induction has to generalize over `n`.

## Main results

* `bellForward`, `bellBackward` with their `k = 0` values and their common recurrence.
* `sum_choose_bell_add_eq_sum_neg_one_pow`.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- The left side, `F(n,k) = ∑_{j ≤ n} C(n,j) B(k+j)`. -/
def bellForward (n k : ℕ) : ℤ := ∑ j ∈ range (n + 1), (n.choose j : ℤ) * Nat.bell (k + j)

/-- The right side, `G(n,k) = ∑_{i ≤ k} (-1)^{k-i} C(k,i) B(n+i+1)`. -/
def bellBackward (n k : ℕ) : ℤ :=
  ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * Nat.bell (n + i + 1)

/-- `F(n,0) = B(n+1)`, which is the Bell recurrence. -/
theorem bellForward_zero (n : ℕ) : bellForward n 0 = Nat.bell (n + 1) := by
  rw [bellForward, bell_succ_eq_sum_choose, Nat.cast_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Nat.zero_add, Nat.cast_mul]

/-- `G(n,0) = B(n+1)`. -/
theorem bellBackward_zero (n : ℕ) : bellBackward n 0 = Nat.bell (n + 1) := by
  rw [bellBackward, Finset.sum_range_one, Nat.sub_self, pow_zero, Nat.choose_self, Nat.cast_one,
    one_mul, one_mul, Nat.add_zero]

/-- The recurrence for the left side: `F(n,k+1) = F(n+1,k) - F(n,k)`. -/
theorem bellForward_succ (n k : ℕ) :
    bellForward n (k + 1) = bellForward (n + 1) k - bellForward n k := by
  have hleft : bellForward (n + 1) k
      = ∑ i ∈ range (n + 1), ((n.choose i : ℤ) + (n.choose (i + 1) : ℤ)) * Nat.bell (k + i + 1)
        + Nat.bell k := by
    rw [bellForward, Finset.sum_range_succ'
      (fun j => ((n + 1).choose j : ℤ) * Nat.bell (k + j)) (n + 1)]
    have h1 : ∑ i ∈ range (n + 1), (((n + 1).choose (i + 1) : ℕ) : ℤ) * Nat.bell (k + (i + 1))
        = ∑ i ∈ range (n + 1),
            ((n.choose i : ℤ) + (n.choose (i + 1) : ℤ)) * Nat.bell (k + i + 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Nat.choose_succ_succ, Nat.cast_add, ← Nat.add_assoc]
    have h2 : (((n + 1).choose 0 : ℕ) : ℤ) * Nat.bell (k + 0) = (Nat.bell k : ℤ) := by
      rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.add_zero]
    rw [h1, h2]
  have hright : bellForward n k
      = ∑ i ∈ range n, (n.choose (i + 1) : ℤ) * Nat.bell (k + i + 1) + Nat.bell k := by
    rw [bellForward, Finset.sum_range_succ'
      (fun j => (n.choose j : ℤ) * Nat.bell (k + j)) n]
    have h1 : ∑ i ∈ range n, ((n.choose (i + 1) : ℕ) : ℤ) * Nat.bell (k + (i + 1))
        = ∑ i ∈ range n, (n.choose (i + 1) : ℤ) * Nat.bell (k + i + 1) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← Nat.add_assoc]
    have h2 : ((n.choose 0 : ℕ) : ℤ) * Nat.bell (k + 0) = (Nat.bell k : ℤ) := by
      rw [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.add_zero]
    rw [h1, h2]
  have htop : ∑ i ∈ range (n + 1), (n.choose (i + 1) : ℤ) * Nat.bell (k + i + 1)
      = ∑ i ∈ range n, (n.choose (i + 1) : ℤ) * Nat.bell (k + i + 1) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, zero_mul, add_zero]
  rw [hleft, hright, bellForward]
  have hsplit : ∑ i ∈ range (n + 1),
        ((n.choose i : ℤ) + (n.choose (i + 1) : ℤ)) * Nat.bell (k + i + 1)
      = ∑ i ∈ range (n + 1), (n.choose i : ℤ) * Nat.bell (k + i + 1)
        + ∑ i ∈ range (n + 1), (n.choose (i + 1) : ℤ) * Nat.bell (k + i + 1) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  rw [hsplit, htop]
  have hshift : ∑ j ∈ range (n + 1), (n.choose j : ℤ) * Nat.bell (k + 1 + j)
      = ∑ i ∈ range (n + 1), (n.choose i : ℤ) * Nat.bell (k + i + 1) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show k + 1 + i = k + i + 1 by omega]
  rw [hshift]
  ring

/-- The recurrence for the right side: `G(n,k+1) = G(n+1,k) - G(n,k)`. -/
theorem bellBackward_succ (n k : ℕ) :
    bellBackward n (k + 1) = bellBackward (n + 1) k - bellBackward n k := by
  have hL : bellBackward n (k + 1)
      = ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) *
            ((k.choose j : ℤ) + (k.choose (j + 1) : ℤ)) * Nat.bell (n + j + 2)
        + (-1 : ℤ) ^ (k + 1) * Nat.bell (n + 1) := by
    rw [bellBackward, Finset.sum_range_succ'
      (fun i => (-1 : ℤ) ^ (k + 1 - i) * ((k + 1).choose i : ℤ) * Nat.bell (n + i + 1)) (k + 1)]
    have h1 : ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k + 1 - (j + 1)) *
          (((k + 1).choose (j + 1) : ℕ) : ℤ) * Nat.bell (n + (j + 1) + 1)
        = ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) *
            ((k.choose j : ℤ) + (k.choose (j + 1) : ℤ)) * Nat.bell (n + j + 2) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show k + 1 - (j + 1) = k - j by omega, Nat.choose_succ_succ, Nat.cast_add,
        show n + (j + 1) + 1 = n + j + 2 by omega]
    have h2 : (-1 : ℤ) ^ (k + 1 - 0) * (((k + 1).choose 0 : ℕ) : ℤ) * Nat.bell (n + 0 + 1)
        = (-1 : ℤ) ^ (k + 1) * Nat.bell (n + 1) := by
      rw [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.add_zero]
    rw [h1, h2]
  have hA : bellBackward (n + 1) k
      = ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * Nat.bell (n + j + 2) := by
    rw [bellBackward]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show n + 1 + j + 1 = n + j + 2 by omega]
  have hB : bellBackward n k
      = ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * Nat.bell (n + j + 1) := by
    rw [bellBackward]
  have hBsplit : bellBackward n k
      = (-1 : ℤ) ^ k * Nat.bell (n + 1)
        + ∑ j ∈ range k, (-1 : ℤ) ^ (k - (j + 1)) * (k.choose (j + 1) : ℤ) *
            Nat.bell (n + j + 2) := by
    rw [hB, Finset.sum_range_succ'
      (fun j => (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * Nat.bell (n + j + 1)) k, add_comm]
    have h1 : ∑ j ∈ range k, (-1 : ℤ) ^ (k - (j + 1)) * ((k.choose (j + 1) : ℕ) : ℤ) *
          Nat.bell (n + (j + 1) + 1)
        = ∑ j ∈ range k, (-1 : ℤ) ^ (k - (j + 1)) * (k.choose (j + 1) : ℤ) *
            Nat.bell (n + j + 2) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [show n + (j + 1) + 1 = n + j + 2 by omega]
    have h2 : (-1 : ℤ) ^ (k - 0) * ((k.choose 0 : ℕ) : ℤ) * Nat.bell (n + 0 + 1)
        = (-1 : ℤ) ^ k * Nat.bell (n + 1) := by
      rw [Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one, Nat.add_zero]
    rw [h1, h2]
  have htop : ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose (j + 1) : ℤ) *
        Nat.bell (n + j + 2)
      = ∑ j ∈ range k, (-1 : ℤ) ^ (k - j) * (k.choose (j + 1) : ℤ) * Nat.bell (n + j + 2) := by
    rw [Finset.sum_range_succ, Nat.choose_succ_self, Nat.cast_zero, mul_zero, zero_mul, add_zero]
  have hsigns : ∑ j ∈ range k, (-1 : ℤ) ^ (k - j) * (k.choose (j + 1) : ℤ) *
        Nat.bell (n + j + 2)
      = -∑ j ∈ range k, (-1 : ℤ) ^ (k - (j + 1)) * (k.choose (j + 1) : ℤ) *
        Nat.bell (n + j + 2) := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hjk : j < k := Finset.mem_range.mp hj
    have hpow : (-1 : ℤ) ^ (k - j) = -(-1 : ℤ) ^ (k - (j + 1)) := by
      rw [show k - j = (k - (j + 1)) + 1 by omega, pow_succ]
      ring
    rw [hpow]
    ring
  have hsplit : ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) *
        ((k.choose j : ℤ) + (k.choose (j + 1) : ℤ)) * Nat.bell (n + j + 2)
      = ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose j : ℤ) * Nat.bell (n + j + 2)
        + ∑ j ∈ range (k + 1), (-1 : ℤ) ^ (k - j) * (k.choose (j + 1) : ℤ) *
            Nat.bell (n + j + 2) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [hL, hsplit, htop, hsigns, hA, hBsplit]
  ring

/-- **The two-sided Bell inversion identity.** -/
theorem sum_choose_bell_add_eq_sum_neg_one_pow (n k : ℕ) :
    ∑ j ∈ range (n + 1), (n.choose j : ℤ) * Nat.bell (k + j) =
      ∑ i ∈ range (k + 1), (-1 : ℤ) ^ (k - i) * (k.choose i : ℤ) * Nat.bell (n + i + 1) := by
  have key : ∀ k n : ℕ, bellForward n k = bellBackward n k := by
    intro k
    induction k with
    | zero => intro n; rw [bellForward_zero, bellBackward_zero]
    | succ k ih =>
      intro n
      rw [bellForward_succ, bellBackward_succ, ih (n + 1), ih n]
  exact key k n

end Fabius
