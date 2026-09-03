import FabiusFunction.QPascalSummation

/-!
# The noncommutative q-binomial theorem

In a semiring, if `Y X = q X Y` with `q` commuting with `X` and `Y`, then

`(X + Y)^n = ∑_{k=0}^{n} [n,k]_q X^{n-k} Y^k`.

This is the defining property of the quantum plane: the Gaussian
coefficients are the structure constants expanding powers of `X + Y` in the
ordered monomial basis `X^{n-k} Y^k`.  The proof multiplies on the left by
`X + Y`; the second `q`-Pascal recurrence (the one built into the definition
of `gaussianBinomial`) then does the bookkeeping through
`sum_gaussianBinomial_succ_mul`, and the only computation is
`Y X^m = q^m X^m Y`.

No commutativity of the ambient semiring is assumed; `q` need only commute
with `X` and `Y`.  In particular the theorem holds in every semiring in which
`q` is central, and over every commutative semiring it is the finite
`q`-binomial theorem in reversed form.

## Main declarations

* `quantumPlane_mul_pow`: `Y X^m = q^m X^m Y`.
* `quantum_binomial`: the noncommutative `q`-binomial theorem.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

open Finset

variable {A : Type*} [Semiring A]

/-- Iterating the commutation relation `Y X = q X Y` along a power of `X`:
`Y X^m = q^m X^m Y`, provided `q` commutes with `X`. -/
theorem quantumPlane_mul_pow {q X Y : A} (hqX : Commute q X) (h : Y * X = q * (X * Y))
    (m : ℕ) :
    Y * X ^ m = q ^ m * (X ^ m * Y) := by
  induction m with
  | zero => simp
  | succ m ih =>
      calc Y * X ^ (m + 1) = (Y * X ^ m) * X := by rw [pow_succ, mul_assoc]
        _ = q ^ m * (X ^ m * (Y * X)) := by rw [ih, mul_assoc, mul_assoc]
        _ = q ^ m * (X ^ m * (q * (X * Y))) := by rw [h]
        _ = q ^ m * (q * (X ^ m * (X * Y))) := by
            rw [← mul_assoc (X ^ m) q, ← (hqX.pow_right m).eq, mul_assoc]
        _ = q ^ (m + 1) * (X ^ (m + 1) * Y) := by
            rw [pow_succ, pow_succ]
            simp only [mul_assoc]

/-- **The noncommutative `q`-binomial theorem.**  If `Y X = q X Y` and `q`
commutes with `X` and `Y`, then `(X + Y)^n = ∑_k [n,k]_q X^{n-k} Y^k`. -/
theorem quantum_binomial {q X Y : A} (hqX : Commute q X) (hqY : Commute q Y)
    (h : Y * X = q * (X * Y)) (n : ℕ) :
    (X + Y) ^ n = ∑ k ∈ range (n + 1), gaussianBinomial q n k * (X ^ (n - k) * Y ^ k) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hcX : ∀ k, Commute (gaussianBinomial q n k) X := fun k => hqX.gaussianBinomial_left n k
      have hcY : ∀ k, Commute (gaussianBinomial q n k) Y := fun k => hqY.gaussianBinomial_left n k
      have hcq : ∀ k, Commute (gaussianBinomial q n k) (q ^ (n - k)) := fun k =>
        ((Commute.refl q).gaussianBinomial_left n k).pow_right _
      rw [pow_succ', ih, Finset.mul_sum, sum_gaussianBinomial_succ_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k hk => ?_
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      rw [show n + 1 - k = n - k + 1 by omega, show n + 1 - (k + 1) = n - k by omega, add_mul]
      congr 1
      · calc X * (gaussianBinomial q n k * (X ^ (n - k) * Y ^ k))
            = (X * gaussianBinomial q n k) * (X ^ (n - k) * Y ^ k) := by rw [mul_assoc]
          _ = (gaussianBinomial q n k * X) * (X ^ (n - k) * Y ^ k) := by rw [(hcX k).eq]
          _ = gaussianBinomial q n k * (X ^ (n - k + 1) * Y ^ k) := by
              rw [pow_succ']
              simp only [mul_assoc]
      · calc Y * (gaussianBinomial q n k * (X ^ (n - k) * Y ^ k))
            = (Y * gaussianBinomial q n k) * (X ^ (n - k) * Y ^ k) := by rw [mul_assoc]
          _ = gaussianBinomial q n k * ((Y * X ^ (n - k)) * Y ^ k) := by
              rw [← (hcY k).eq]
              simp only [mul_assoc]
          _ = gaussianBinomial q n k * (q ^ (n - k) * (X ^ (n - k) * Y ^ (k + 1))) := by
              rw [quantumPlane_mul_pow hqX h, pow_succ']
              simp only [mul_assoc]
          _ = q ^ (n - k) * gaussianBinomial q n k * (X ^ (n - k) * Y ^ (k + 1)) := by
              rw [← mul_assoc, (hcq k).eq]

end Fabius
