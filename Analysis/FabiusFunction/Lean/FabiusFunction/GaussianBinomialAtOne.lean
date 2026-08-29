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

end Fabius
