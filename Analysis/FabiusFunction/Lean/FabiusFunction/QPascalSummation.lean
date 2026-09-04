import FabiusFunction.FiniteQBinomialCore
import Mathlib.Tactic.Abel

/-!
# q-Pascal summation and the commutation of Gaussian coefficients

Two small but widely reusable facts about the division-free Gaussian
coefficient `gaussianBinomial q n k`.

* **q-Pascal summation.**  A sum `∑_k [n+1,k]_q f k` over the `(n+1)`-st row
  splits, by either `q`-Pascal recurrence, into two sums over the `n`-th row:

  `∑_{k≤n+1} [n+1,k] f k = ∑_{k≤n} [n,k] f k + ∑_{k≤n} q^{n-k} [n,k] f (k+1)`

  over every semiring, and

  `∑_{k≤n+1} [n+1,k] f k = ∑_{k≤n} q^k [n,k] f k + ∑_{k≤n} [n,k] f (k+1)`

  over every commutative semiring.  These are the coefficient-free forms of
  the recurrences for `q`-binomial-type generating polynomials; the
  noncommutative `q`-binomial theorem and the Rogers–Szegő recurrence are
  both instances.
* **Commutation.**  Gaussian coefficients are polynomials in `q` with natural
  coefficients, so they commute with everything `q` commutes with.  This is
  what allows them to be used as scalars in a noncommutative algebra.

## Main declarations

* `sum_gaussianBinomial_succ_mul`, `sum_gaussianBinomial_succ_mul'`.
* `Commute.gaussianBinomial_left`, `Commute.gaussianBinomial_right`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

/-- **q-Pascal summation, first form.**  Over every semiring, with the
coefficients on the left and the weight `q^{n-k}` on the shifted term. -/
theorem sum_gaussianBinomial_succ_mul {R : Type*} [Semiring R] (q : R) (n : ℕ) (f : ℕ → R) :
    ∑ k ∈ range (n + 1 + 1), gaussianBinomial q (n + 1) k * f k =
      ∑ k ∈ range (n + 1), gaussianBinomial q n k * f k +
        ∑ k ∈ range (n + 1), q ^ (n - k) * gaussianBinomial q n k * f (k + 1) := by
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [gaussianBinomial_succ_succ, add_mul, Finset.sum_add_distrib,
    gaussianBinomial_zero_right, one_mul]
  rw [Finset.sum_range_succ' (fun k => gaussianBinomial q n k * f k) n,
    Finset.sum_range_succ (fun k => gaussianBinomial q n (k + 1) * f (k + 1)) n,
    gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n), zero_mul, add_zero,
    gaussianBinomial_zero_right, one_mul]
  abel

/-- **q-Pascal summation, second form.**  Over every commutative semiring,
with the weight `q^k` on the unshifted term. -/
theorem sum_gaussianBinomial_succ_mul' {R : Type*} [CommSemiring R] (q : R) (n : ℕ)
    (f : ℕ → R) :
    ∑ k ∈ range (n + 1 + 1), gaussianBinomial q (n + 1) k * f k =
      ∑ k ∈ range (n + 1), q ^ k * gaussianBinomial q n k * f k +
        ∑ k ∈ range (n + 1), gaussianBinomial q n k * f (k + 1) := by
  rw [Finset.sum_range_succ' _ (n + 1)]
  simp only [gaussianBinomial_succ_succ_alt, add_mul, Finset.sum_add_distrib,
    gaussianBinomial_zero_right, one_mul]
  rw [Finset.sum_range_succ' (fun k => q ^ k * gaussianBinomial q n k * f k) n,
    Finset.sum_range_succ (fun k => q ^ (k + 1) * gaussianBinomial q n (k + 1) * f (k + 1)) n,
    gaussianBinomial_eq_zero_of_lt q (Nat.lt_succ_self n)]
  simp only [pow_zero, one_mul, mul_zero, zero_mul, add_zero, gaussianBinomial_zero_right]
  abel

/-- Gaussian coefficients commute with everything `q` commutes with. -/
theorem _root_.Commute.gaussianBinomial_left {R : Type*} [Semiring R] {q x : R}
    (h : Commute q x) (n k : ℕ) :
    Commute (gaussianBinomial q n k) x := by
  induction n generalizing k with
  | zero =>
      cases k with
      | zero => simp
      | succ k => simp
  | succ n ih =>
      cases k with
      | zero => simp
      | succ k =>
          rw [gaussianBinomial_succ_succ]
          exact (ih (k + 1)).add_left ((h.pow_left _).mul_left (ih k))

/-- Everything `q` commutes with commutes with the Gaussian coefficients. -/
theorem _root_.Commute.gaussianBinomial_right {R : Type*} [Semiring R] {q x : R}
    (h : Commute x q) (n k : ℕ) :
    Commute x (gaussianBinomial q n k) :=
  (h.symm.gaussianBinomial_left n k).symm

end Fabius
