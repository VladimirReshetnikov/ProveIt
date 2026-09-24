import Mathlib.RingTheory.PowerSeries.Binomial
import Mathlib.Tactic.FieldSimp

/-!
# Formal binomial roots

The rational formal-series identity in `osq:nm:lem:binomial`, using
Mathlib's binomial series and exponent-addition identity.
-/

namespace Surreal.FormalBinomialRoots

/-- Natural powers multiply the exponent of the native formal binomial series. -/
theorem binomialSeries_pow {K : Type*} [Field K] [CharZero K] (r : K) (n : ℕ) :
    PowerSeries.binomialSeries K r ^ n = PowerSeries.binomialSeries K ((n : K) * r) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
      PowerSeries.binomialSeries_add]

/-- The reciprocal-integer binomial series is an exact formal root, over any characteristic-zero field. -/
theorem binomialSeries_root {K : Type*} [Field K] [CharZero K] (m : ℕ) (hm : m ≠ 0) :
    PowerSeries.binomialSeries K (1 / (m : K)) ^ m = 1 + PowerSeries.X := by
  rw [binomialSeries_pow, mul_one_div_cancel (Nat.cast_ne_zero.mpr hm)]
  simpa only [Nat.cast_one, pow_one] using (PowerSeries.binomialSeries_nat (R := K) (A := K) 1)

end Surreal.FormalBinomialRoots
