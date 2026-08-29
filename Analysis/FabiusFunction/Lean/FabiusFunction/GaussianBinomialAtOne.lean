import FabiusFunction.FiniteQBinomialCore
import Mathlib.Data.Nat.Choose.Basic

/-!
# The Gaussian coefficient at `q = 1`

At `q = 1` the `q`-Pascal recurrence

`[n+1, k+1]_q = [n, k+1]_q + q^{n-k}·[n, k]_q`

loses its weight and becomes ordinary Pascal, so the Gaussian
coefficient degenerates to the binomial one.  The statement is proved
first over `ℕ`, where it is a bare induction, and then transported to
an arbitrary semiring by the functoriality of `gaussianBinomial`
under ring homomorphisms — so no ring-specific argument is repeated.

This is the `q = 1` shadow that every `q`-analogue in the corpus is
measured against: the graded bit-position aggregation of
`BitPositionQBinomial` collapses to `Fabius.card_filter_binaryWeight_eq`
exactly here.

* `gaussianBinomial_nat_one` — the `ℕ`-valued core;
* `gaussianBinomial_one` — **the general form**, over any semiring;
* `gaussianBinomial_one_eq_natCast_choose` — the cast-shaped variant.
-/

set_option autoImplicit false

namespace Fabius

/-- **The Gaussian coefficient at `q = 1`, over `ℕ`.**  The `q`-Pascal
recurrence degenerates to Pascal's rule. -/
theorem gaussianBinomial_nat_one (n k : ℕ) :
    gaussianBinomial (1 : ℕ) n k = n.choose k := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => rfl
      | succ k => rfl
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussianBinomial_succ_succ, one_pow, one_mul, ih, ih,
            Nat.choose_succ_succ]
          exact Nat.add_comm _ _

/-- **The Gaussian coefficient at `q = 1`**, over an arbitrary
semiring: it is the binomial coefficient.  Transported from the `ℕ`
core along `Nat.castRingHom`, whose action on `1` is `map_one`. -/
theorem gaussianBinomial_one {R : Type*} [Semiring R] (n k : ℕ) :
    gaussianBinomial (1 : R) n k = (n.choose k : R) := by
  have h := map_gaussianBinomial (Nat.castRingHom R) (1 : ℕ) n k
  rw [map_one] at h
  rw [← h, gaussianBinomial_nat_one]
  rfl

/-- The same statement with the cast written out, matching the shape
in which the graded `q`-binomial aggregation consumes it. -/
theorem gaussianBinomial_one_eq_natCast_choose {R : Type*}
    [Semiring R] (n k : ℕ) :
    gaussianBinomial (1 : R) n k = ((n.choose k : ℕ) : R) :=
  gaussianBinomial_one n k

/-- Above the diagonal the coefficient vanishes at `q = 1`, matching
`Nat.choose_eq_zero_of_lt`. -/
theorem gaussianBinomial_one_eq_zero_of_lt {R : Type*} [Semiring R]
    {n k : ℕ} (h : n < k) : gaussianBinomial (1 : R) n k = 0 := by
  rw [gaussianBinomial_one, Nat.choose_eq_zero_of_lt h]
  exact Nat.cast_zero

/-! ## The `q`-Pochhammer symbol at the same specializations -/

/-- **The finite `q`-Pochhammer symbol at `q = 1`**: every factor
collapses to `1 - a`, so `(a; 1)_n = (1-a)^n`. -/
theorem finiteQPochhammerIn_one {R : Type*} [CommRing R] (a : R)
    (n : ℕ) : finiteQPochhammerIn a (1 : R) n = (1 - a) ^ n := by
  rw [finiteQPochhammerIn]
  rw [Finset.prod_congr rfl
    (fun j _ => by rw [one_pow, mul_one] :
      ∀ j ∈ Finset.range n, 1 - a * (1 : R) ^ j = 1 - a)]
  rw [Finset.prod_const, Finset.card_range]

/-- At `a = 0` the product is empty of content: every factor is one. -/
@[simp] theorem finiteQPochhammerIn_zero_left {R : Type*} [CommRing R]
    (q : R) (n : ℕ) : finiteQPochhammerIn (0 : R) q n = 1 := by
  rw [finiteQPochhammerIn]
  refine Finset.prod_eq_one fun j _ => ?_
  rw [zero_mul, sub_zero]

/-- At `a = 1` the `j = 0` factor is `1 - q^0 = 0`, so the product
vanishes as soon as it is nonempty. -/
theorem finiteQPochhammerIn_one_left {R : Type*} [CommRing R] (q : R)
    (n : ℕ) : finiteQPochhammerIn (1 : R) q (n + 1) = 0 := by
  rw [finiteQPochhammerIn]
  refine Finset.prod_eq_zero
    (Finset.mem_range.mpr (Nat.succ_pos n)) ?_
  rw [pow_zero, mul_one, sub_self]

/-- **The `q`-binomial theorem degenerates to the binomial theorem.**
Specializing `finite_qBinomial_theorem` at `q = 1` — where the weight
`q^{C(k,2)}` disappears and the Gaussian coefficient becomes the
binomial one — gives `∑_{k≤n} (-1)^k·C(n,k)·z^k = (1-z)^n`.

This is the consistency check the whole `q`-layer is measured
against. -/
theorem sum_neg_one_pow_choose_mul_pow {R : Type*} [CommRing R]
    (z : R) (n : ℕ) :
    (∑ k ∈ Finset.range (n + 1),
      (-1 : R) ^ k * (n.choose k : R) * z ^ k) = (1 - z) ^ n := by
  have h := finite_qBinomial_theorem (1 : R) z n
  rw [finiteQPochhammerIn_one] at h
  rw [← h]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [one_pow, gaussianBinomial_one]
  ring

end Fabius
