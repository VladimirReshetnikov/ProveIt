import FabiusFunction.FiniteQBinomialCore
import Mathlib.Data.Nat.Choose.Basic

/-!
# Gaussian coefficients and finite q-Pochhammer products at `q = -1`

At the second root of unity the Gaussian triangle collapses by parity.  If
`n = 2a + ε` and `k = 2b + δ`, with `ε, δ ∈ {0,1}`, then

* the even-row/odd-column entry vanishes;
* every other entry is the ordinary binomial coefficient `a.choose b`.

The proof below keeps the four parity classes visible.  Two applications of
q-Pascal turn an odd row into the next even row: the two odd-column terms
cancel, while the even-column terms combine by ordinary Pascal.  This is the
denominator-free `q = -1` instance of q-Lucas, valid over every commutative
ring, including positive characteristic.

The companion product identities expose the same collapse before coefficient
extraction:

`(z; -1)_(2a) = (1 - z^2)^a`,

`(z; -1)_(2a+1) = (1 - z^2)^a (1-z)`.

## Main results

* `gaussianBinomial_neg_one_even_even` and
  `gaussianBinomial_neg_one_even_odd` evaluate an even row;
* `gaussianBinomial_neg_one_odd_even` and
  `gaussianBinomial_neg_one_odd_odd` evaluate an odd row;
* `finiteQPochhammerIn_neg_one_even` and
  `finiteQPochhammerIn_neg_one_odd` pair the alternating factors.
-/

set_option autoImplicit false

namespace Fabius

private theorem gaussianBinomial_neg_one_rows
    {R : Type*} [CommRing R] (a : ℕ) :
    (∀ b : ℕ,
      gaussianBinomial (-1 : R) (2 * a) (2 * b) = (a.choose b : R)) ∧
    (∀ b : ℕ,
      gaussianBinomial (-1 : R) (2 * a) (2 * b + 1) = 0) ∧
    (∀ b : ℕ,
      gaussianBinomial (-1 : R) (2 * a + 1) (2 * b) = (a.choose b : R)) ∧
    (∀ b : ℕ,
      gaussianBinomial (-1 : R) (2 * a + 1) (2 * b + 1) =
        (a.choose b : R)) := by
  induction a with
  | zero =>
      constructor
      · intro b
        cases b with
        | zero => simp
        | succ b =>
            rw [gaussianBinomial_eq_zero_of_lt (-1 : R) (by omega)]
            simp
      constructor
      · intro b
        rw [gaussianBinomial_eq_zero_of_lt (-1 : R) (by omega)]
      constructor
      · intro b
        cases b with
        | zero => simp
        | succ b =>
            rw [gaussianBinomial_eq_zero_of_lt (-1 : R) (by omega)]
            simp
      · intro b
        cases b with
        | zero => simp
        | succ b =>
            rw [gaussianBinomial_eq_zero_of_lt (-1 : R) (by omega)]
            simp
  | succ a ih =>
      rcases ih with ⟨hee, heo, hoe, hoo⟩
      have hnextEvenEven : ∀ b : ℕ,
          gaussianBinomial (-1 : R) (2 * (a + 1)) (2 * b) =
            ((a + 1).choose b : R) := by
        intro b
        cases b with
        | zero => simp
        | succ b =>
            have heven : Even (2 * b + 1 + 1) := ⟨b + 1, by omega⟩
            rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
              show 2 * (b + 1) = (2 * b + 1) + 1 by omega,
              gaussianBinomial_succ_succ_alt, heven.neg_one_pow,
              one_mul, show 2 * b + 1 + 1 = 2 * (b + 1) by omega,
              hoe (b + 1), hoo b, Nat.choose_succ_succ, Nat.cast_add]
            ring
      have hnextEvenOdd : ∀ b : ℕ,
          gaussianBinomial (-1 : R) (2 * (a + 1)) (2 * b + 1) = 0 := by
        intro b
        have hodd : Odd (2 * b + 1) := ⟨b, by omega⟩
        rw [show 2 * (a + 1) = (2 * a + 1) + 1 by omega,
          show 2 * b + 1 = 2 * b + 1 by rfl,
          gaussianBinomial_succ_succ_alt, hodd.neg_one_pow,
          hoo b, hoe b]
        ring
      have hnextOddEven : ∀ b : ℕ,
          gaussianBinomial (-1 : R) (2 * (a + 1) + 1) (2 * b) =
            ((a + 1).choose b : R) := by
        intro b
        cases b with
        | zero => simp
        | succ b =>
            have heven : Even (2 * b + 1 + 1) := ⟨b + 1, by omega⟩
            rw [show 2 * (b + 1) = (2 * b + 1) + 1 by omega,
              gaussianBinomial_succ_succ_alt, heven.neg_one_pow,
              one_mul, show 2 * b + 1 + 1 = 2 * (b + 1) by omega,
              hnextEvenEven (b + 1), hnextEvenOdd b, add_zero]
      have hnextOddOdd : ∀ b : ℕ,
          gaussianBinomial (-1 : R) (2 * (a + 1) + 1) (2 * b + 1) =
            ((a + 1).choose b : R) := by
        intro b
        have hodd : Odd (2 * b + 1) := ⟨b, by omega⟩
        rw [show 2 * b + 1 = 2 * b + 1 by rfl,
          gaussianBinomial_succ_succ_alt, hodd.neg_one_pow,
          hnextEvenOdd b, hnextEvenEven b]
        simp
      exact ⟨hnextEvenEven, hnextEvenOdd, hnextOddEven, hnextOddOdd⟩

/-- **Even row, even column at `q = -1`.**  The Gaussian coefficient
`[2a choose 2b]_{-1}` is the ordinary coefficient `[a choose b]` over every
commutative ring. -/
theorem gaussianBinomial_neg_one_even_even
    {R : Type*} [CommRing R] (a b : ℕ) :
    gaussianBinomial (-1 : R) (2 * a) (2 * b) = (a.choose b : R) := by
  exact (gaussianBinomial_neg_one_rows a).1 b

/-- **Even row, odd column at `q = -1`.**  Every Gaussian coefficient
`[2a choose 2b+1]_{-1}` vanishes. -/
theorem gaussianBinomial_neg_one_even_odd
    {R : Type*} [CommRing R] (a b : ℕ) :
    gaussianBinomial (-1 : R) (2 * a) (2 * b + 1) = 0 := by
  exact (gaussianBinomial_neg_one_rows a).2.1 b

/-- **Odd row, even column at `q = -1`.**  The Gaussian coefficient
`[2a+1 choose 2b]_{-1}` is `[a choose b]`. -/
theorem gaussianBinomial_neg_one_odd_even
    {R : Type*} [CommRing R] (a b : ℕ) :
    gaussianBinomial (-1 : R) (2 * a + 1) (2 * b) = (a.choose b : R) := by
  exact (gaussianBinomial_neg_one_rows a).2.2.1 b

/-- **Odd row, odd column at `q = -1`.**  The adjacent coefficient
`[2a+1 choose 2b+1]_{-1}` has the same value `[a choose b]`. -/
theorem gaussianBinomial_neg_one_odd_odd
    {R : Type*} [CommRing R] (a b : ℕ) :
    gaussianBinomial (-1 : R) (2 * a + 1) (2 * b + 1) =
      (a.choose b : R) := by
  exact (gaussianBinomial_neg_one_rows a).2.2.2 b

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
