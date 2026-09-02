import Mathlib.Tactic.Zify
import Mathlib.Tactic.LinearCombination
import FabiusFunction.StirlingBasisChange

/-!
# Lah numbers

The (unsigned) Lah numbers `L(n,k)` convert rising factorials into falling
factorials,

`X (X+1) ⋯ (X+n-1) = ∑_{k ≤ n} L(n,k) · X (X-1) ⋯ (X-k+1)`,

and conversely with alternating signs.  We define them by the triangular
recurrence

`L(n+1,k+1) = (n+k+1) L(n,k+1) + L(n,k)`,  `L(0,0) = 1`,

which is exactly what multiplying the rising factorial by `X + n` does to
the falling-factorial coefficients, since
`(X)_k (X+n) = (X)_{k+1} + (n+k) (X)_k`.  From the polynomial identity and
the uniqueness of coefficients in a triangular basis we obtain

* the closed form `L(n+1,k+1) (k+1)! = (n+1)! C(n,k)`, i.e.
  `L(n,k) = C(n-1,k-1) n!/k!`;
* the signed inverse conversion
  `(X)_n = ∑_{k ≤ n} (-1)^(n-k) L(n,k) · X (X+1) ⋯ (X+k-1)`;
* the Lah inversion `∑_{j ≤ n} (-1)^(j-k) L(n,j) L(j,k) = δ_{nk}`;
* the factorization through the two Stirling triangles,
  `L(n,k) = ∑_{j ≤ n} c(n,j) S(j,k)`.

All polynomial identities hold over an arbitrary commutative ring.

## Main results

* `lahNumber`, `lahNumber_succ_succ`, `lahNumber_eq_zero_of_lt`,
  `lahNumber_self`, `lahNumber_succ_succ_mul_factorial`.
* `ascPochhammer_eq_sum_lahNumber_mul_descPochhammer`,
  `descPochhammer_eq_sum_lahNumber_mul_ascPochhammer`.
* `sum_range_lahNumber_mul_lahNumber`: Lah inversion.
* `lahNumber_eq_sum_stirlingFirst_mul_stirlingSecond`: the Stirling
  factorization.
-/

set_option autoImplicit false

open Finset Polynomial

namespace Fabius

/-- The unsigned Lah numbers, defined by the triangular recurrence
`L(n+1,k+1) = (n+k+1) L(n,k+1) + L(n,k)` with `L(0,0) = 1` and zero boundary. -/
def lahNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 0
  | n + 1, k + 1 => (n + k + 1) * lahNumber n (k + 1) + lahNumber n k

@[simp] theorem lahNumber_zero_zero : lahNumber 0 0 = 1 := rfl

@[simp] theorem lahNumber_zero_succ (k : ℕ) : lahNumber 0 (k + 1) = 0 := rfl

@[simp] theorem lahNumber_succ_zero (n : ℕ) : lahNumber (n + 1) 0 = 0 := rfl

/-- The Lah recurrence `L(n+1,k+1) = (n+k+1) L(n,k+1) + L(n,k)`. -/
theorem lahNumber_succ_succ (n k : ℕ) :
    lahNumber (n + 1) (k + 1) = (n + k + 1) * lahNumber n (k + 1) + lahNumber n k := rfl

/-- Lah numbers vanish above the diagonal. -/
theorem lahNumber_eq_zero_of_lt : ∀ {n k : ℕ}, n < k → lahNumber n k = 0
  | _, 0, h => absurd h (Nat.not_lt_zero _)
  | 0, _ + 1, _ => rfl
  | n + 1, k + 1, h => by
    rw [lahNumber_succ_succ, lahNumber_eq_zero_of_lt (Nat.lt_of_succ_lt_succ h),
      lahNumber_eq_zero_of_lt (Nat.lt_of_succ_lt h), mul_zero]

/-- The diagonal Lah numbers are one. -/
theorem lahNumber_self (n : ℕ) : lahNumber n n = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [lahNumber_succ_succ, lahNumber_eq_zero_of_lt (Nat.lt_succ_self n), mul_zero, zero_add, ih]

/-- **Closed form of the Lah numbers:** `L(n+1,k+1) · (k+1)! = (n+1)! · C(n,k)`,
that is, `L(n,k) = C(n-1,k-1) · n!/k!` for `1 ≤ k ≤ n`. -/
theorem lahNumber_succ_succ_mul_factorial (n k : ℕ) :
    lahNumber (n + 1) (k + 1) * (k + 1).factorial = (n + 1).factorial * n.choose k := by
  induction n generalizing k with
  | zero =>
    cases k with
    | zero => decide
    | succ k =>
      rw [lahNumber_eq_zero_of_lt (by omega), Nat.choose_eq_zero_of_lt (by omega)]
      simp
  | succ n ih =>
    rw [lahNumber_succ_succ, add_mul, mul_assoc, ih k]
    cases k with
    | zero =>
      rw [lahNumber_succ_zero, zero_mul, add_zero, Nat.choose_zero_right, Nat.choose_zero_right,
        Nat.factorial_succ (n + 1)]
      ring
    | succ j =>
      have hb := ih j
      rw [Nat.factorial_succ (j + 1), mul_comm (j + 1 + 1) (j + 1).factorial,
        ← mul_assoc (lahNumber (n + 1) (j + 1)), hb, Nat.factorial_succ (n + 1),
        Nat.choose_succ_succ' n j]
      have hc := Nat.choose_succ_right_eq n j
      rcases le_or_gt j n with hjn | hjn
      · obtain ⟨d, rfl⟩ : ∃ d, n = j + d := ⟨n - j, by omega⟩
        rw [Nat.add_sub_cancel_left] at hc
        zify at hc ⊢
        linear_combination (((j + d + 1).factorial : ℤ)) * hc
      · rw [Nat.choose_eq_zero_of_lt hjn, Nat.choose_eq_zero_of_lt (by omega)]
        simp

/-- The one-step relation `(X)_k · (X + n) = (X)_{k+1} + (n + k) (X)_k`. -/
theorem descPochhammer_mul_X_add_natCast {R : Type*} [CommRing R] (k n : ℕ) :
    descPochhammer R k * (X + (n : R[X])) =
      descPochhammer R (k + 1) + ((n + k : ℕ) : R[X]) * descPochhammer R k := by
  rw [descPochhammer_succ_right]
  push_cast
  ring

/-- **Rising factorials in the falling-factorial basis:**
`X (X+1) ⋯ (X+n-1) = ∑_{k ≤ n} L(n,k) · X (X-1) ⋯ (X-k+1)`, over any commutative
ring. -/
theorem ascPochhammer_eq_sum_lahNumber_mul_descPochhammer (R : Type*) [CommRing R] (n : ℕ) :
    ascPochhammer R n =
      ∑ k ∈ Finset.range (n + 1), (lahNumber n k : R[X]) * descPochhammer R k := by
  induction n with
  | zero => simp [ascPochhammer_zero, descPochhammer_zero]
  | succ n ih =>
    have hsplit : ascPochhammer R (n + 1)
        = ∑ k ∈ Finset.range (n + 1), (lahNumber n k : R[X]) * descPochhammer R (k + 1)
          + ∑ k ∈ Finset.range (n + 1),
            (((n + k : ℕ) : R[X]) * lahNumber n k) * descPochhammer R k := by
      rw [ascPochhammer_succ_right, ih, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [mul_assoc, descPochhammer_mul_X_add_natCast]
      ring
    have hsecond : ∑ k ∈ Finset.range (n + 1),
          (((n + k : ℕ) : R[X]) * lahNumber n k) * descPochhammer R k
        = ∑ k ∈ Finset.range (n + 1),
          (((n + (k + 1) : ℕ) : R[X]) * lahNumber n (k + 1)) * descPochhammer R (k + 1) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ,
        lahNumber_eq_zero_of_lt (Nat.lt_succ_self n)]
      have hz : (((n + 0 : ℕ) : R[X]) * lahNumber n 0) * descPochhammer R 0 = 0 := by
        cases n <;> simp
      rw [hz]
      simp
    have hrhs : ∑ k ∈ Finset.range (n + 2), (lahNumber (n + 1) k : R[X]) * descPochhammer R k
        = ∑ k ∈ Finset.range (n + 1),
            (((n + (k + 1) : ℕ) : R[X]) * lahNumber n (k + 1)) * descPochhammer R (k + 1)
          + ∑ k ∈ Finset.range (n + 1), (lahNumber n k : R[X]) * descPochhammer R (k + 1) := by
      rw [Finset.sum_range_succ', lahNumber_succ_zero, Nat.cast_zero, zero_mul, add_zero,
        ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [lahNumber_succ_succ]
      push_cast
      ring
    rw [hsplit, hsecond, hrhs, add_comm]

/-- **Falling factorials in the rising-factorial basis:**
`X (X-1) ⋯ (X-n+1) = ∑_{k ≤ n} (-1)^(n-k) L(n,k) · X (X+1) ⋯ (X+k-1)`. -/
theorem descPochhammer_eq_sum_lahNumber_mul_ascPochhammer (R : Type*) [CommRing R] (n : ℕ) :
    descPochhammer R n = ∑ k ∈ Finset.range (n + 1),
      ((-1) ^ (n - k) * lahNumber n k : R[X]) * ascPochhammer R k := by
  have h := congrArg (fun p : R[X] => p.comp (-X))
    (ascPochhammer_eq_sum_lahNumber_mul_descPochhammer R n)
  simp only [ascPochhammer_comp_neg_X, finsetSum_comp, mul_comp, natCast_comp,
    descPochhammer_comp_neg_X] at h
  calc descPochhammer R n = (-1) ^ n * ((-1) ^ n * descPochhammer R n) := by
        rw [← mul_assoc, ← mul_pow]
        simp
    _ = (-1) ^ n * ∑ k ∈ Finset.range (n + 1),
          (lahNumber n k : R[X]) * ((-1) ^ k * ascPochhammer R k) := by rw [h]
    _ = ∑ k ∈ Finset.range (n + 1),
          ((-1) ^ (n - k) * lahNumber n k : R[X]) * ascPochhammer R k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k hk => ?_
        rw [neg_one_pow_sub_eq_neg_one_pow_add (Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)),
          pow_add]
        ring

/-- **Lah inversion:** `∑_{j ≤ n} (-1)^(j-k) L(n,j) L(j,k) = δ_{nk}`: the signed
Lah matrix is its own inverse.  This is read off from the two conversion
formulas by uniqueness of rising-factorial coefficients. -/
theorem sum_range_lahNumber_mul_lahNumber (n k : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (lahNumber n j : ℤ) * ((-1) ^ (j - k) * lahNumber j k)) =
      if n = k then 1 else 0 := by
  rcases lt_or_ge n k with hnk | hkn
  · rw [if_neg (by omega)]
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    rw [lahNumber_eq_zero_of_lt (show j < k by omega), Nat.cast_zero, mul_zero, mul_zero]
  · -- the rising factorial expanded twice along the rising-factorial basis
    have hexp : ascPochhammer ℤ n = ∑ i ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1),
          (lahNumber n j : ℤ[X]) * ((-1) ^ (j - i) * lahNumber j i : ℤ[X])) *
            ascPochhammer ℤ i := by
      rw [← sum_mul_sum_mul_eq (fun j => (lahNumber n j : ℤ[X]))
        (fun j i => ((-1) ^ (j - i) * lahNumber j i : ℤ[X])) (ascPochhammer ℤ) n
        (fun j i hji => by simp [lahNumber_eq_zero_of_lt hji])]
      rw [ascPochhammer_eq_sum_lahNumber_mul_descPochhammer]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [descPochhammer_eq_sum_lahNumber_mul_ascPochhammer ℤ j]
    -- coefficients in the rising-factorial basis are unique
    have huniq := eq_of_sum_C_mul_eq_sum_C_mul (R := ℤ) (ascPochhammer ℤ)
      (fun k => coeff_ascPochhammer_self k) (fun k m h => coeff_ascPochhammer_of_lt h) n
      (fun i => ∑ j ∈ Finset.range (n + 1),
        (lahNumber n j : ℤ) * ((-1) ^ (j - i) * lahNumber j i))
      (fun i => if n = i then 1 else 0) ?_ k hkn
    · simpa using huniq
    · simp only [apply_ite C, map_one, map_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq,
        Finset.mem_range, lt_add_one, if_true]
      simp only [map_sum, map_mul, map_pow, map_neg, map_one, C_eq_natCast]
      exact hexp.symm

/-- **The Stirling factorization of the Lah numbers:**
`L(n,k) = ∑_{j ≤ n} c(n,j) S(j,k)`: converting rising factorials to powers and
powers to falling factorials composes the two Stirling triangles. -/
theorem lahNumber_eq_sum_stirlingFirst_mul_stirlingSecond (n k : ℕ) :
    lahNumber n k = ∑ j ∈ Finset.range (n + 1), Nat.stirlingFirst n j * Nat.stirlingSecond j k := by
  rcases lt_or_ge n k with hnk | hkn
  · rw [lahNumber_eq_zero_of_lt hnk]
    symm
    apply Finset.sum_eq_zero
    intro j hj
    have hjn : j < n + 1 := Finset.mem_range.mp hj
    rw [Nat.stirlingSecond_eq_zero_of_lt (show j < k by omega), mul_zero]
  · -- the rising factorial through the monomial basis into the falling basis
    have hexp : ascPochhammer ℤ n = ∑ i ∈ Finset.range (n + 1),
        (∑ j ∈ Finset.range (n + 1),
          (Nat.stirlingFirst n j : ℤ[X]) * (Nat.stirlingSecond j i : ℤ[X])) *
            descPochhammer ℤ i := by
      rw [← sum_mul_sum_mul_eq (fun j => (Nat.stirlingFirst n j : ℤ[X]))
        (fun j i => (Nat.stirlingSecond j i : ℤ[X])) (descPochhammer ℤ) n
        (fun j i hji => by simp [Nat.stirlingSecond_eq_zero_of_lt hji])]
      rw [ascPochhammer_eq_sum_monomial_stirlingFirst]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← X_pow_eq_sum_stirlingSecond_mul_descPochhammer, ← C_mul_X_pow_eq_monomial,
        C_eq_natCast]
    have huniq := eq_of_sum_C_mul_eq_sum_C_mul (R := ℤ) (descPochhammer ℤ)
      (fun k => coeff_descPochhammer_self k) (fun k m h => coeff_descPochhammer_of_lt h) n
      (fun i => (lahNumber n i : ℤ))
      (fun i => ∑ j ∈ Finset.range (n + 1),
        (Nat.stirlingFirst n j : ℤ) * (Nat.stirlingSecond j i : ℤ)) ?_ k hkn
    · exact_mod_cast huniq
    · simp only [map_sum, map_mul, C_eq_natCast]
      rw [← hexp, ← ascPochhammer_eq_sum_lahNumber_mul_descPochhammer]

end Fabius
