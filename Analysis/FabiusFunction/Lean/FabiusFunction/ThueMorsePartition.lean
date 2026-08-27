import FabiusFunction.ThueMorseHessenberg
import FabiusFunction.ExponentialPartition

/-!
# The partition and Bell-polynomial formulae for the Thue–Morse sign

Exponentiating the Euler transform writes each sign as a finite sum
over weighted partitions.  We formalize this without any analytic
step: the partition sum obeys the *marked-part recurrence* — the
coefficient recurrence of `exp(∑ xⱼzʲ)` — proved by pure finite
combinatorics; the ruler convolution says the Thue–Morse sign obeys the
same recurrence; and a division-by-`n` uniqueness lemma identifies the
two.

* `eq_of_ruler_recurrence_ring` — reusable: over **any** ring with no
  zero divisors and characteristic zero, the recurrence
  `n·c(n) = -∑_{k≤n} L(k)·c(n-k)` together with `c(0)` pins the whole
  sequence down.  Nothing is divided: the proof only cancels the
  nonzero element `(n : R)`, which needs no inverse.
* `eq_of_ruler_recurrence` — the same statement over a
  characteristic-zero field, a corollary of the ring version.
* `thueMorseSign_eq_of_ruler_recurrence` — the `ℤ`-valued instance of
  the ring version: `ε` is the *unique* integer sequence with
  `ε(0) = 1` obeying the ruler recurrence.
* `weightedPartitions n` and `partitionExpSum_recurrence`, imported from
  `ExponentialPartition`, provide the reusable exponential-formula skeleton
  over every commutative `ℚ`-algebra.
* `thueMorse_partition_formula_field` — the atlas's partition formula
  `ε(n) = ∑_{∑j·mⱼ=n} ∏ (1/mⱼ!)(-aⱼ/j)^{mⱼ}` over an arbitrary
  characteristic-zero field, with `thueMorse_partition_formula` its
  `ℚ`-valued corollary.
* `thueMorse_bell_formula_field` — the Bell-polynomial form
  `n!·ε(n) = ∑_λ n!/(∏ mⱼ!(j!)^{mⱼ})·∏(-(j-1)!·aⱼ)^{mⱼ}`, again over
  an arbitrary characteristic-zero field, with `thueMorse_bell_formula`
  its `ℚ`-valued corollary.

## What needs division, and what does not

The uniqueness lemma never divides — it multiplies both recurrences out
and cancels the regular element `(n : R)` — so it lives over any
characteristic-zero ring without zero divisors, `ℤ` included.

The generic `partitionExpSum` takes reciprocal factorials in `ℚ` and lets
them act by scalars.  Thus its definition and marked-part recurrence need
only a commutative `ℚ`-algebra; no cancellation in the target is used.
The ruler specialization below additionally divides by the part size `j`,
so its printed field-valued formula retains the natural characteristic-zero
field assumptions.  `partitionExpSum_eq_sum_div` is the bridge from the
generic scalar formulation to that familiar quotient notation.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-- **Uniqueness of the ruler recurrence** over a characteristic-zero
ring without zero divisors: `n·c(n) = -∑_{k=1}^n L(k)·c(n-k)` together
with `c(0)` pins down the whole sequence.

This is the general form of `eq_of_ruler_recurrence`: no division is
performed anywhere, only cancellation of the nonzero natural `(n : R)`,
so no inverses — and in particular no field structure — are needed.  The
`ℤ`-valued instance is `thueMorseSign_eq_of_ruler_recurrence`. -/
theorem eq_of_ruler_recurrence_ring {R : Type*} [Ring R]
    [NoZeroDivisors R] [CharZero R]
    (L c d : ℕ → R) (h0 : c 0 = d 0)
    (hc : ∀ n : ℕ, 1 ≤ n →
      (n : R) * c n = -∑ k ∈ Icc 1 n, L k * c (n - k))
    (hd : ∀ n : ℕ, 1 ≤ n →
      (n : R) * d n = -∑ k ∈ Icc 1 n, L k * d (n - k)) :
    ∀ n, c n = d n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · exact h0
      · have hsum : ∑ k ∈ Icc 1 n, L k * c (n - k) =
            ∑ k ∈ Icc 1 n, L k * d (n - k) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          have := Finset.mem_Icc.mp hk
          rw [ih (n - k) (by omega)]
        have hmul : (n : R) * c n = (n : R) * d n := by
          rw [hc n hn, hd n hn, hsum]
        exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (by omega)) hmul

/-- **Uniqueness of the ruler recurrence** over a characteristic-zero
field: `n·c(n) = -∑_{k=1}^n L(k)·c(n-k)` together with `c(0)` pins down
the whole sequence.  A corollary of `eq_of_ruler_recurrence_ring`, since
a field has no zero divisors. -/
theorem eq_of_ruler_recurrence {F : Type*} [Field F] [CharZero F]
    (L c d : ℕ → F) (h0 : c 0 = d 0)
    (hc : ∀ n : ℕ, 1 ≤ n →
      (n : F) * c n = -∑ k ∈ Icc 1 n, L k * c (n - k))
    (hd : ∀ n : ℕ, 1 ≤ n →
      (n : F) * d n = -∑ k ∈ Icc 1 n, L k * d (n - k)) :
    ∀ n, c n = d n :=
  eq_of_ruler_recurrence_ring L c d h0 hc hd

/-- **The Thue–Morse sign is the unique integer solution of the ruler
recurrence.**  Any `d : ℕ → ℤ` with `d 0 = 1` and
`n·d(n) = -∑_{k=1}^n a_k·d(n-k)` for `n ≥ 1` equals `ε`.

This is the payoff of stating the uniqueness lemma over a ring: `ℤ` is
not a field, so the statement is out of reach of
`eq_of_ruler_recurrence`, yet no division is needed to prove it. -/
theorem thueMorseSign_eq_of_ruler_recurrence (d : ℕ → ℤ) (h0 : d 0 = 1)
    (hd : ∀ n : ℕ, 1 ≤ n →
      (n : ℤ) * d n = -∑ k ∈ Icc 1 n, rulerCoeff k * d (n - k)) :
    ∀ n, thueMorseSign n = d n := by
  refine eq_of_ruler_recurrence_ring rulerCoeff thueMorseSign d ?_ ?_ hd
  · simp [thueMorseSign, binaryWeight, h0]
  · intro n _
    exact ruler_convolution n

/-- The Thue–Morse sign satisfies the ruler recurrence in any ring, by
casting the integer identity `ruler_convolution`. -/
private theorem sign_ruler_cast {R : Type*} [Ring R] (n : ℕ) :
    (n : R) * ((thueMorseSign n : ℤ) : R) =
      -∑ k ∈ Icc 1 n, ((rulerCoeff k : ℤ) : R) *
        ((thueMorseSign (n - k) : ℤ) : R) := by
  have h := congrArg (fun t : ℤ => (t : R)) (ruler_convolution n)
  simp only [Int.cast_mul, Int.cast_neg, Int.cast_sum,
    Int.cast_natCast] at h
  rw [h]
  congr 1

/-- The partition sum with `xⱼ = -aⱼ/j` satisfies the same ruler
recurrence, over any characteristic-zero field. -/
private theorem partition_ruler_cast {F : Type*} [Field F] [CharZero F]
    (n : ℕ) :
    (n : F) * partitionExpSum
        (fun j => -((rulerCoeff j : ℤ) : F) / j) n =
      -∑ k ∈ Icc 1 n, ((rulerCoeff k : ℤ) : F) *
        partitionExpSum (fun j => -((rulerCoeff j : ℤ) : F) / j) (n - k) := by
  rw [partitionExpSum_recurrence _ n, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' := Finset.mem_Icc.mp hk
  have hkne : (k : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/-- **The partition formula** (`eq:partition-formula`) over an arbitrary
characteristic-zero field:
`ε(n) = ∑_{m₁+2m₂+⋯=n} ∏ⱼ (1/mⱼ!)·(-aⱼ/j)^{mⱼ}`. -/
theorem thueMorse_partition_formula_field {F : Type*} [Field F]
    [CharZero F] (n : ℕ) :
    ((thueMorseSign n : ℤ) : F) =
      ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
        (-((rulerCoeff j : ℤ) : F) / j) ^ f j / (f j).factorial := by
  have h := eq_of_ruler_recurrence_ring
    (fun k => ((rulerCoeff k : ℤ) : F))
    (fun n => ((thueMorseSign n : ℤ) : F))
    (partitionExpSum (fun j => -((rulerCoeff j : ℤ) : F) / j))
    (by simp [thueMorseSign, binaryWeight])
    (fun n _ => sign_ruler_cast n)
    (fun n _ => partition_ruler_cast n)
    n
  rw [h, partitionExpSum_eq_sum_div]

/-- **The partition formula** (`eq:partition-formula`) over `ℚ`:
`ε(n) = ∑_{m₁+2m₂+⋯=n} ∏ⱼ (1/mⱼ!)·(-aⱼ/j)^{mⱼ}`. -/
theorem thueMorse_partition_formula (n : ℕ) :
    ((thueMorseSign n : ℤ) : ℚ) =
      ∑ f ∈ weightedPartitions n, ∏ j ∈ Icc 1 n,
        (-((rulerCoeff j : ℤ) : ℚ) / j) ^ f j / (f j).factorial :=
  thueMorse_partition_formula_field n

/-- **The Bell-polynomial form** (`eq:Bell-coefficient`) over an
arbitrary characteristic-zero field:
`n!·ε(n) = ∑_λ n!/(∏ⱼ mⱼ!·(j!)^{mⱼ}) · ∏ⱼ (-(j-1)!·aⱼ)^{mⱼ}` — the
complete exponential Bell polynomial `B_n` evaluated at
`xⱼ = -(j-1)!·aⱼ`. -/
theorem thueMorse_bell_formula_field {F : Type*} [Field F] [CharZero F]
    (n : ℕ) :
    (n.factorial : F) * ((thueMorseSign n : ℤ) : F) =
      ∑ f ∈ weightedPartitions n,
        (n.factorial : F) /
            (∏ j ∈ Icc 1 n,
              ((f j).factorial : F) * (j.factorial : F) ^ f j) *
          ∏ j ∈ Icc 1 n,
            (-(((j - 1).factorial : F) * ((rulerCoeff j : ℤ) : F))) ^ f j := by
  rw [thueMorse_partition_formula_field (F := F) n, Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  have hprod : ∏ j ∈ Icc 1 n,
      (-((rulerCoeff j : ℤ) : F) / j) ^ f j / (f j).factorial =
      ∏ j ∈ Icc 1 n,
        ((-(((j - 1).factorial : F) * ((rulerCoeff j : ℤ) : F))) ^ f j /
          (((f j).factorial : F) * ((j.factorial : F)) ^ f j)) := by
    refine Finset.prod_congr rfl fun j hj => ?_
    have hj' := Finset.mem_Icc.mp hj
    have hjfact : (j.factorial : F) =
        (j : F) * (((j - 1).factorial : F)) := by
      rw [← Nat.cast_mul, ← Nat.mul_factorial_pred (by omega)]
    have hjne : (j : F) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hfne : (((j - 1).factorial : F)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have hmne : (((f j).factorial : F)) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have h1 : ((j : F)) ^ (f j) ≠ 0 := pow_ne_zero _ hjne
    have h2 : (((j - 1).factorial : F)) ^ (f j) ≠ 0 := pow_ne_zero _ hfne
    rw [show (-(((j - 1).factorial : F) * ((rulerCoeff j : ℤ) : F))) =
        (-((rulerCoeff j : ℤ) : F)) * (((j - 1).factorial : F)) from by
      ring]
    rw [div_pow, mul_pow, hjfact, mul_pow]
    field_simp
  rw [hprod, Finset.prod_div_distrib]
  ring

/-- **The Bell-polynomial form** (`eq:Bell-coefficient`) over `ℚ`:
`n!·ε(n) = ∑_λ n!/(∏ⱼ mⱼ!·(j!)^{mⱼ}) · ∏ⱼ (-(j-1)!·aⱼ)^{mⱼ}` — the
complete exponential Bell polynomial `B_n` evaluated at
`xⱼ = -(j-1)!·aⱼ`. -/
theorem thueMorse_bell_formula (n : ℕ) :
    (n.factorial : ℚ) * ((thueMorseSign n : ℤ) : ℚ) =
      ∑ f ∈ weightedPartitions n,
        (n.factorial : ℚ) /
            (∏ j ∈ Icc 1 n,
              ((f j).factorial : ℚ) * (j.factorial : ℚ) ^ f j) *
          ∏ j ∈ Icc 1 n,
            (-(((j - 1).factorial : ℚ) * ((rulerCoeff j : ℤ) : ℚ))) ^ f j :=
  thueMorse_bell_formula_field n

end Fabius
