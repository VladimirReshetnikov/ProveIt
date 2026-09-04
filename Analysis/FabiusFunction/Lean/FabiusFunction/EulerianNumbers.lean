import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.Zify
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FieldSimp
import FabiusFunction.StirlingBasisChange

/-!
# Eulerian numbers and Worpitzky's identity

The Eulerian number `A(n,k)` counts the permutations of `n` letters with
exactly `k` descents.  Mathlib has no Eulerian numbers; we define them by the
triangular recurrence

`A(n+1,k) = (k+1) A(n,k) + (n+1-k) A(n,k-1)`,  `A(0,0) = 1`,

(insert the largest letter into a permutation of `n` letters), and prove
the identities that make them a change-of-basis matrix between powers and
shifted binomial coefficients:

* the boundary values `A(n,0) = 1`, the vanishing `A(n,k) = 0` for
  `1 ≤ n ≤ k`, and the row sum `∑_k A(n,k) = n!`;
* **Worpitzky's identity** `m^n = ∑_{k ≤ n} A(n,k) C(m+k, n)` for natural
  numbers, proved by induction from the one-step relation
  `m C(m+k,n) = (n-k) C(m+k+1,n+1) + (k+1) C(m+k,n+1)`, and then as a
  polynomial identity `X^n = ∑_k A(n,k) · C(X+k, n)` in `ℚ[X]`, since both
  sides agree at every natural number;
* the power-sum formula
  `∑_{r ≤ m} r^(n+1) = ∑_{k ≤ n+1} A(n+1,k) C(m+k+1, n+2)`, from Worpitzky
  and the hockey-stick identity.

## Main results

* `eulerianNumber`, `eulerianNumber_succ_succ`, `eulerianNumber_succ_left`,
  `eulerianNumber_eq_zero_of_le`, `eulerianNumber_zero_right`,
  `sum_eulerianNumber_eq_factorial`.
* `mul_choose_add_eq`, `worpitzky_nat`, `binomialPoly`, `worpitzky_polynomial`.
* `sum_range_choose_add_eq`, `sum_range_pow_succ_eq_sum_eulerianNumber`.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-- The Eulerian numbers `A(n,k)`, the number of permutations of `n` letters
with `k` descents, defined by the insertion recurrence
`A(n+1,k+1) = (k+2) A(n,k+1) + (n-k) A(n,k)` and `A(n+1,0) = A(n,0)`, with
`A(0,0) = 1` and `A(0,k+1) = 0`. -/
def eulerianNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, 0 => eulerianNumber n 0
  | n + 1, k + 1 => (k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k

/-- The initial Eulerian number is `A(0,0) = 1`. -/
@[simp] theorem eulerianNumber_zero_zero : eulerianNumber 0 0 = 1 := rfl

/-- Every positive-index entry in the zeroth Eulerian row vanishes. -/
@[simp] theorem eulerianNumber_zero_succ (k : ℕ) : eulerianNumber 0 (k + 1) = 0 := rfl

/-- The zeroth Eulerian column is preserved when the row index is incremented. -/
theorem eulerianNumber_succ_zero (n : ℕ) : eulerianNumber (n + 1) 0 = eulerianNumber n 0 := rfl

/-- The insertion recurrence in the form `A(n+1,k+1) = (k+2) A(n,k+1) + (n-k) A(n,k)`. -/
theorem eulerianNumber_succ_succ (n k : ℕ) :
    eulerianNumber (n + 1) (k + 1) =
      (k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k := rfl

/-- The first column is constant: `A(n,0) = 1`. -/
@[simp] theorem eulerianNumber_zero_right (n : ℕ) : eulerianNumber n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [eulerianNumber_succ_zero, ih]

/-- Eulerian numbers vanish on and above the diagonal: `A(n,k) = 0` for
`1 ≤ n ≤ k`. -/
theorem eulerianNumber_eq_zero_of_le : ∀ {n k : ℕ}, 1 ≤ n → n ≤ k → eulerianNumber n k = 0
  | 0, _, h, _ => absurd h (by omega)
  | _ + 1, 0, _, h => absurd h (by omega)
  | n + 1, k + 1, _, h => by
    rw [eulerianNumber_succ_succ]
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      simp
    · rw [eulerianNumber_eq_zero_of_le (k := k + 1) hn (by omega), mul_zero, zero_add]
      rcases Nat.lt_or_ge n k with hnk | hnk
      · rw [eulerianNumber_eq_zero_of_le (k := k) hn (by omega), mul_zero]
      · have hk : k = n := by omega
        subst hk
        simp

/-- `A(n, n+1) = 0` for every `n`. -/
theorem eulerianNumber_succ_self (n : ℕ) : eulerianNumber n (n + 1) = 0 := by
  cases n with
  | zero => rfl
  | succ n => exact eulerianNumber_eq_zero_of_le (by omega) (by omega)

/-- The Eulerian recurrence in the textbook indexing
`A(n+1,k) = (k+1) A(n,k) + (n+1-k) A(n,k-1)`, valid for `1 ≤ k`. -/
theorem eulerianNumber_succ_left (n k : ℕ) (hk : 1 ≤ k) :
    eulerianNumber (n + 1) k =
      (k + 1) * eulerianNumber n k + (n + 1 - k) * eulerianNumber n (k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  rw [eulerianNumber_succ_succ, Nat.add_sub_cancel]
  have h1 : n + 1 - (j + 1) = n - j := by omega
  rw [h1]

/-- Row sums: `∑_{k ≤ n} A(n,k) = n!`. -/
theorem sum_eulerianNumber_eq_factorial (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), eulerianNumber n k = n.factorial := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hpeel : ∑ k ∈ Finset.range (n + 2), eulerianNumber (n + 1) k
        = eulerianNumber n 0 + ∑ k ∈ Finset.range (n + 1),
            ((k + 2) * eulerianNumber n (k + 1) + (n - k) * eulerianNumber n k) := by
      rw [Finset.sum_range_succ', eulerianNumber_succ_zero, add_comm]
      simp only [eulerianNumber_succ_succ]
    have hshift : eulerianNumber n 0 + ∑ k ∈ Finset.range (n + 1), (k + 2) * eulerianNumber n (k + 1)
        = ∑ k ∈ Finset.range (n + 1), (k + 1) * eulerianNumber n k := by
      have h := Finset.sum_range_succ' (fun k => (k + 1) * eulerianNumber n k) (n + 1)
      rw [Finset.sum_range_succ, eulerianNumber_succ_self, mul_zero, add_zero] at h
      have e1 : ∑ k ∈ Finset.range (n + 1), (k + 2) * eulerianNumber n (k + 1)
          = ∑ k ∈ Finset.range (n + 1), (k + 1 + 1) * eulerianNumber n (k + 1) :=
        Finset.sum_congr rfl fun k _ => by ring
      rw [h, add_comm, e1]
      ring
    rw [hpeel, Finset.sum_add_distrib, ← add_assoc, hshift, ← Finset.sum_add_distrib,
      Nat.factorial_succ, ← ih, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    rw [← add_mul]
    congr 1
    omega

/-! ### Worpitzky's identity -/

/-- The one-step relation behind Worpitzky's identity:
`m · C(m+k, n) = (n-k) · C(m+k+1, n+1) + (k+1) · C(m+k, n+1)` for `k ≤ n`. -/
theorem mul_choose_add_eq (m n k : ℕ) (hk : k ≤ n) :
    m * (m + k).choose n =
      (n - k) * (m + k + 1).choose (n + 1) + (k + 1) * (m + k).choose (n + 1) := by
  rcases Nat.lt_or_ge (m + k) n with hlt | hge
  · rw [Nat.choose_eq_zero_of_lt hlt, Nat.choose_eq_zero_of_lt (show m + k + 1 < n + 1 by omega),
      Nat.choose_eq_zero_of_lt (show m + k < n + 1 by omega)]
    simp
  · have hc1 := Nat.choose_succ_right_eq (m + k) n
    have hc2 := Nat.choose_succ_succ' (m + k) n
    rw [hc2]
    zify [hk, hge] at hc1 ⊢
    linear_combination (-1 : ℤ) * hc1

/-- **Worpitzky's identity** for natural numbers:
`m^n = ∑_{k ≤ n} A(n,k) · C(m+k, n)` (the term `k = n` vanishes for `n ≥ 1`). -/
theorem worpitzky_nat (n m : ℕ) :
    m ^ n = ∑ k ∈ Finset.range (n + 1), eulerianNumber n k * (m + k).choose n := by
  induction n generalizing m with
  | zero => simp
  | succ n ih =>
    have hstep : m ^ (n + 1)
        = ∑ k ∈ Finset.range (n + 1), eulerianNumber n k *
            ((n - k) * (m + k + 1).choose (n + 1) + (k + 1) * (m + k).choose (n + 1)) := by
      rw [pow_succ', ih m, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [← mul_choose_add_eq m n k hkn]
      ring
    -- the right-hand side, with its first term peeled and the recurrence applied
    have hrhs : ∑ k ∈ Finset.range (n + 2), eulerianNumber (n + 1) k * (m + k).choose (n + 1)
        = ∑ k ∈ Finset.range (n + 1), (k + 2) * eulerianNumber n (k + 1) * (m + (k + 1)).choose (n + 1)
          + ∑ k ∈ Finset.range (n + 1), (n - k) * eulerianNumber n k * (m + (k + 1)).choose (n + 1)
          + eulerianNumber n 0 * (m + 0).choose (n + 1) := by
      rw [Finset.sum_range_succ', eulerianNumber_succ_zero, ← Finset.sum_add_distrib]
      congr 1
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [eulerianNumber_succ_succ]
      ring
    -- the second half of the left-hand side, shifted by one
    have hsecond : ∑ k ∈ Finset.range (n + 1), eulerianNumber n k * ((k + 1) * (m + k).choose (n + 1))
        = ∑ k ∈ Finset.range (n + 1),
            (k + 2) * eulerianNumber n (k + 1) * (m + (k + 1)).choose (n + 1)
          + eulerianNumber n 0 * (m + 0).choose (n + 1) := by
      conv_lhs => rw [Finset.sum_range_succ']
      conv_rhs => rw [Finset.sum_range_succ, eulerianNumber_succ_self, mul_zero, zero_mul, add_zero]
      congr 1
      · refine Finset.sum_congr rfl fun k _ => ?_
        ring
      · ring
    have hfirst : ∑ k ∈ Finset.range (n + 1), eulerianNumber n k * ((n - k) * (m + k + 1).choose (n + 1))
        = ∑ k ∈ Finset.range (n + 1),
            (n - k) * eulerianNumber n k * (m + (k + 1)).choose (n + 1) := by
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [show m + (k + 1) = m + k + 1 by ring]
      ring
    rw [hstep, hrhs]
    simp only [mul_add]
    rw [Finset.sum_add_distrib, hfirst, hsecond]
    ring

/-- The binomial polynomial `C(X + k, n) = (X+k)(X+k-1)⋯(X+k-n+1) / n!` in `ℚ[X]`. -/
noncomputable def binomialPoly (n k : ℕ) : ℚ[X] :=
  C (1 / (n.factorial : ℚ)) * (descPochhammer ℚ n).comp (X + (k : ℚ[X]))

/-- At a natural number `m`, `C(X + k, n)` evaluates to `C(m+k, n)`. -/
theorem binomialPoly_eval_natCast (n k m : ℕ) :
    (binomialPoly n k).eval (m : ℚ) = (m + k).choose n := by
  rw [binomialPoly, eval_mul, eval_C, eval_comp, eval_add, eval_X, eval_natCast, ← Nat.cast_add,
    descPochhammer_eval_eq_descFactorial, Nat.descFactorial_eq_factorial_mul_choose]
  have hn : (n.factorial : ℚ) ≠ 0 := by positivity
  push_cast
  field_simp

/-- **Worpitzky's identity** as a polynomial identity:
`X^n = ∑_{k ≤ n} A(n,k) · C(X+k, n)` in `ℚ[X]`. -/
theorem worpitzky_polynomial (n : ℕ) :
    (X : ℚ[X]) ^ n = ∑ k ∈ Finset.range (n + 1), (eulerianNumber n k : ℚ[X]) * binomialPoly n k := by
  apply Polynomial.eq_of_infinite_eval_eq
  apply Set.infinite_of_injective_forall_mem (f := fun m : ℕ => (m : ℚ)) Nat.cast_injective
  intro m
  simp only [Set.mem_setOf_eq, eval_pow, eval_X, eval_finsetSum, eval_mul, eval_natCast,
    binomialPoly_eval_natCast]
  exact_mod_cast worpitzky_nat n m

/-! ### Power sums -/

/-- A shifted hockey-stick identity: for `k ≤ n`,
`∑_{i ≤ N} C(i + k, n) = C(N + k + 1, n + 1)`. -/
theorem sum_range_choose_add_eq (N n k : ℕ) (hk : k ≤ n) :
    ∑ i ∈ Finset.range (N + 1), (i + k).choose n = (N + k + 1).choose (n + 1) := by
  rw [← Nat.sum_Icc_choose (N + k) n, Finset.range_eq_Ico, Finset.sum_Ico_add' (fun j => j.choose n) 0 (N + 1) k]
  rw [zero_add, show N + 1 + k = N + k + 1 by ring, Finset.Ico_add_one_right_eq_Icc]
  symm
  apply Finset.sum_subset
  · intro j hj
    rw [Finset.mem_Icc] at hj ⊢
    omega
  · intro j hj hj'
    rw [Finset.mem_Icc] at hj hj'
    exact Nat.choose_eq_zero_of_lt (by omega)

/-- **Power sums through Eulerian numbers:**
`∑_{r ≤ m} r^(n+1) = ∑_{k ≤ n+1} A(n+1,k) · C(m+k+1, n+2)`. -/
theorem sum_range_pow_succ_eq_sum_eulerianNumber (m n : ℕ) :
    ∑ r ∈ Finset.range (m + 1), r ^ (n + 1) =
      ∑ k ∈ Finset.range (n + 2), eulerianNumber (n + 1) k * (m + k + 1).choose (n + 2) := by
  calc ∑ r ∈ Finset.range (m + 1), r ^ (n + 1)
      = ∑ r ∈ Finset.range (m + 1), ∑ k ∈ Finset.range (n + 2),
          eulerianNumber (n + 1) k * (r + k).choose (n + 1) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        exact worpitzky_nat (n + 1) r
    _ = ∑ k ∈ Finset.range (n + 2), eulerianNumber (n + 1) k *
          ∑ r ∈ Finset.range (m + 1), (r + k).choose (n + 1) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.mul_sum]
    _ = _ := by
        refine Finset.sum_congr rfl fun k hk => ?_
        have hkn : k ≤ n + 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
        rw [sum_range_choose_add_eq m (n + 1) k hkn]

/-! ### Eulerian polynomials -/

/-- The Eulerian polynomial `A_n(t) = ∑_{k ≤ n} A(n,k) t^k` over a commutative ring. -/
noncomputable def eulerianPolynomial (R : Type*) [CommRing R] (n : ℕ) : R[X] :=
  ∑ k ∈ Finset.range (n + 1), (eulerianNumber n k : R[X]) * X ^ k

/-- `A_n(1) = n!`. -/
theorem eulerianPolynomial_eval_one (R : Type*) [CommRing R] (n : ℕ) :
    (eulerianPolynomial R n).eval 1 = n.factorial := by
  rw [← sum_eulerianNumber_eq_factorial, eulerianPolynomial, eval_finsetSum]
  push_cast
  refine Finset.sum_congr rfl fun k _ => ?_
  simp

end Fabius
