import FabiusFunction.QBinomialReciprocity
import Mathlib.Data.Nat.Choose.Basic

/-!
# Gaussian coefficients and finite q-Pochhammer products at `q = -1`

The value of a Gaussian coefficient at the second root of unity is an
ordinary binomial coefficient, except in the even-row/odd-column parity where
it vanishes.  Together with the reciprocity theorem imported from
`QBinomialReciprocity`, this module gives the complete four-case table over
every commutative ring:

* `gaussianBinomial_neg_one_even_even` gives
  `[2a choose 2b]_(-1) = (a choose b)`;
* `gaussianBinomial_neg_one_even_odd_eq_zero` gives
  `[2a choose 2b+1]_(-1) = 0`;
* `gaussianBinomial_neg_one_odd_even` gives
  `[2a+1 choose 2b]_(-1) = (a choose b)`;
* `gaussianBinomial_neg_one_odd_odd` gives
  `[2a+1 choose 2b+1]_(-1) = (a choose b)`.

The same parity collapse already occurs in the finite product:

* `finiteQPochhammerIn_neg_one_even` pairs consecutive factors to give
  `(z; -1)_(2a) = (1 - z^2)^a`;
* `finiteQPochhammerIn_neg_one_odd` leaves one final even factor and gives
  `(z; -1)_(2a+1) = (1 - z^2)^a (1-z)`.

All four value statements are total in `a` and `b`; when the column lies above the
row, both the recursive Gaussian coefficient and the ordinary binomial
coefficient are zero.  The proof never forms a factorial quotient at
`q = -1`.  Instead, two applications of the denominator-free q-Pascal
recurrence turn the even-even case into ordinary Pascal, and the other cases
follow from the intervening odd row.  Thus the proof reuses the reciprocity
vanishing theorem rather than duplicating a simultaneous four-row induction.
-/

set_option autoImplicit false

namespace Fabius

/-- **Even row, even column at `q = -1`.**  Over every commutative ring,

`[2a choose 2b]_(-1) = (a choose b)`.

The identity is total, including `b > a`. -/
theorem gaussianBinomial_neg_one_even_even
    {R : Type*} [CommRing R] (a b : ℕ) :
    gaussianBinomial (-1 : R) (2 * a) (2 * b) = (a.choose b : R) := by
  induction a generalizing b with
  | zero =>
      cases b with
      | zero => simp
      | succ b =>
          have hzero :
              gaussianBinomial (-1 : R) (2 * 0) (2 * Nat.succ b) = 0 :=
            gaussianBinomial_eq_zero_of_lt (-1 : R) (by omega)
          rw [hzero]
          simp
  | succ a ih =>
      cases b with
      | zero => simp
      | succ b =>
          have heven : Even (2 * b + 1 + 1) := ⟨b + 1, by omega⟩
          have hcolEven : 2 * b + 1 + 1 = 2 * Nat.succ b := by omega
          have hOddEven :
              gaussianBinomial (-1 : R) (2 * a + 1) (2 * b + 1 + 1) =
                (a.choose (Nat.succ b) : R) := by
            rw [gaussianBinomial_succ_succ_alt, heven.neg_one_pow, one_mul,
              hcolEven, ih,
              gaussianBinomial_neg_one_even_odd_eq_zero, add_zero]
          have hOddOdd :
              gaussianBinomial (-1 : R) (2 * a + 1) (2 * b + 1) =
                (a.choose b : R) := by
            rw [gaussianBinomial_succ_succ_alt,
              gaussianBinomial_neg_one_even_odd_eq_zero, mul_zero, zero_add, ih]
          rw [show 2 * Nat.succ a = (2 * a + 1) + 1 by omega,
            show 2 * Nat.succ b = (2 * b + 1) + 1 by omega,
            gaussianBinomial_succ_succ_alt, heven.neg_one_pow, one_mul,
            hOddEven, hOddOdd, Nat.choose_succ_succ, Nat.cast_add]
          exact add_comm _ _

/-- **Odd row, even column at `q = -1`.**  Over every commutative ring,

`[2a+1 choose 2b]_(-1) = (a choose b)`.

The identity is total, including `b > a`. -/
theorem gaussianBinomial_neg_one_odd_even
    {R : Type*} [CommRing R] (a b : ℕ) :
    gaussianBinomial (-1 : R) (2 * a + 1) (2 * b) = (a.choose b : R) := by
  cases b with
  | zero => simp
  | succ b =>
      have heven : Even (2 * b + 1 + 1) := ⟨b + 1, by omega⟩
      rw [show 2 * Nat.succ b = (2 * b + 1) + 1 by omega,
        gaussianBinomial_succ_succ_alt, heven.neg_one_pow, one_mul,
        gaussianBinomial_neg_one_even_odd_eq_zero, add_zero,
        show 2 * b + 1 + 1 = 2 * (b + 1) by omega,
        gaussianBinomial_neg_one_even_even]

/-- **Odd row, odd column at `q = -1`.**  Over every commutative ring,

`[2a+1 choose 2b+1]_(-1) = (a choose b)`.

The identity is total, including `b > a`. -/
theorem gaussianBinomial_neg_one_odd_odd
    {R : Type*} [CommRing R] (a b : ℕ) :
    gaussianBinomial (-1 : R) (2 * a + 1) (2 * b + 1) =
      (a.choose b : R) := by
  rw [gaussianBinomial_succ_succ_alt,
    gaussianBinomial_neg_one_even_odd_eq_zero, mul_zero, zero_add,
    gaussianBinomial_neg_one_even_even]

/-- **Paired finite q-Pochhammer product at `q = -1`.**  Consecutive
factors multiply to `(1-z)(1+z) = 1-z^2`, so
`(z;-1)_{2a} = (1-z^2)^a`. -/
theorem finiteQPochhammerIn_neg_one_even
    {R : Type*} [CommRing R] (z : R) (a : ℕ) :
    finiteQPochhammerIn z (-1 : R) (2 * a) = (1 - z ^ 2) ^ a := by
  induction a with
  | zero => simp
  | succ a ih =>
      have heven : Even (2 * a) := ⟨a, by omega⟩
      have hodd : Odd (2 * a + 1) := ⟨a, by omega⟩
      rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
        finiteQPochhammerIn_succ, finiteQPochhammerIn_succ, ih,
        heven.neg_one_pow, hodd.neg_one_pow, pow_succ]
      ring

/-- **Odd finite q-Pochhammer product at `q = -1`.**  One unpaired even
factor remains: `(z;-1)_{2a+1} = (1-z^2)^a (1-z)`. -/
theorem finiteQPochhammerIn_neg_one_odd
    {R : Type*} [CommRing R] (z : R) (a : ℕ) :
    finiteQPochhammerIn z (-1 : R) (2 * a + 1) =
      (1 - z ^ 2) ^ a * (1 - z) := by
  have heven : Even (2 * a) := ⟨a, by omega⟩
  rw [finiteQPochhammerIn_succ, finiteQPochhammerIn_neg_one_even,
    heven.neg_one_pow, mul_one]

end Fabius
