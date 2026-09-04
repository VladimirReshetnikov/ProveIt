import FabiusFunction.DiamondPower
import Mathlib.RingTheory.PowerSeries.Exp

/-!
# Binomial inversion in exponential generating functions

The corpus already had binomial inversion as a statement about sequences.  This module adds
the generating-function form the source displays alongside it:

`B(z) = e^z A(z)`  iff  `b_n = ∑_k C(n,k) a_k`   (`egfA_eq_exp_mul_iff`),
`A(z) = e^{-z} B(z)`  iff  `a_n = ∑_k (-1)^{n-k} C(n,k) b_k`   (`egfA_eq_altSeries_mul_iff`),

over any commutative `ℚ`-algebra, with `e^{-z}` written as the exponential generating function
`altSeries` of `(-1)^n` and shown to invert `exp` (`exp_mul_altSeries`).

Both are the same one-line argument: multiplying exponential generating functions is binomial
convolution (`Fabius.egfA_mul`), convolving against the constant sequence `1` or against
`(-1)^n` produces exactly the two displayed sums once the summation index is reflected
(`binomialConv_one_left`, `binomialConv_altSeries_left`), and a sequence is determined by its
exponential generating function (`seq_eq_of_egfA_eq`).

The coefficient cancellation in `exp_mul_altSeries` is the binomial theorem at
`1 + (-1) = 0` and is valid over any commutative ring. The ordinary exponential
generating functions themselves require the stated `ℚ`-algebra structure, which
supplies the inverse factorials.

## Main results

* `exp_eq_egfA_one`, `altSeries`, `exp_mul_altSeries`.
* `binomialConv_one_left`, `binomialConv_altSeries_left`.
* `egfA_eq_exp_mul_iff`, `egfA_eq_altSeries_mul_iff`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section InversionEGF

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- `e^z` is the exponential generating function of the constant sequence `1`. -/
theorem exp_eq_egfA_one : exp A = egfA A fun _ => (1 : A) := by
  refine PowerSeries.ext fun n => ?_
  rw [coeff_exp, coeff_egfA, mul_one]

/-- The exponential generating function of `(-1)^n`, i.e. `e^{-z}`. -/
noncomputable def altSeries : A⟦X⟧ := egfA A fun n => (-1 : A) ^ n

omit [Algebra ℚ A] in
/-- Convolving against the constant sequence `1` is the forward binomial transform,
over any commutative ring. -/
theorem binomialConv_one_left (a : ℕ → A) (n : ℕ) :
    Bell.binomialConv (fun _ => (1 : A)) a n = ∑ k ∈ range (n + 1), (n.choose k : A) * a k := by
  have hrefl := Finset.sum_range_reflect (fun k => (n.choose k : A) * a k) (n + 1)
  rw [Bell.binomialConv_eq_sum_range, ← hrefl]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm hkn, one_mul]

omit [Algebra ℚ A] in
/-- Convolving against `(-1)^n` is the backward binomial transform,
over any commutative ring. -/
theorem binomialConv_altSeries_left (b : ℕ → A) (n : ℕ) :
    Bell.binomialConv (fun i => (-1 : A) ^ i) b n =
      ∑ k ∈ range (n + 1), (-1 : A) ^ (n - k) * (n.choose k : A) * b k := by
  have hrefl := Finset.sum_range_reflect
    (fun k => (-1 : A) ^ (n - k) * (n.choose k : A) * b k) (n + 1)
  rw [Bell.binomialConv_eq_sum_range, ← hrefl]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [Nat.add_sub_cancel]
  rw [Nat.choose_symm hkn, Nat.sub_sub_self hkn]
  ring

/-- **`e^{-z}` inverts `e^{z}`**, by the binomial theorem at `1 + (-1) = 0`. -/
theorem exp_mul_altSeries : exp A * altSeries A = 1 := by
  rw [exp_eq_egfA_one, altSeries, egfA_mul]
  have hone : Bell.binomialConv (fun _ => (1 : A)) (fun n => (-1 : A) ^ n) = Bell.unitSeq A := by
    funext n
    rw [binomialConv_one_left]
    have hzero : ((-1 : A) + 1) ^ n =
        ∑ k ∈ range (n + 1), (-1 : A) ^ k * (1 : A) ^ (n - k) * (n.choose k : A) :=
      add_pow _ _ _
    rw [neg_add_cancel] at hzero
    have hsum : ∑ k ∈ range (n + 1), (n.choose k : A) * (-1 : A) ^ k = (0 : A) ^ n := by
      rw [hzero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [one_pow, mul_one]
      ring
    rw [hsum]
    cases n with
    | zero => rw [pow_zero, Bell.unitSeq_zero]
    | succ m => rw [zero_pow (Nat.succ_ne_zero m), Bell.unitSeq_succ]
  rw [hone]
  exact egfA_unitSeq A

/-- **The forward form:** `B(z) = e^z A(z)` exactly when `b` is the binomial transform of `a`. -/
theorem egfA_eq_exp_mul_iff (a b : ℕ → A) :
    egfA A b = exp A * egfA A a ↔ ∀ n, b n = ∑ k ∈ range (n + 1), (n.choose k : A) * a k := by
  rw [exp_eq_egfA_one, egfA_mul]
  constructor
  · intro h n
    rw [seq_eq_of_egfA_eq A h, binomialConv_one_left]
  · intro h
    congr 1
    funext n
    rw [binomialConv_one_left, h n]

/-- **The backward form:** `A(z) = e^{-z} B(z)` exactly when `a` is the inverse binomial
transform of `b`. -/
theorem egfA_eq_altSeries_mul_iff (a b : ℕ → A) :
    egfA A a = altSeries A * egfA A b ↔
      ∀ n, a n = ∑ k ∈ range (n + 1), (-1 : A) ^ (n - k) * (n.choose k : A) * b k := by
  rw [altSeries, egfA_mul]
  constructor
  · intro h n
    rw [seq_eq_of_egfA_eq A h, binomialConv_altSeries_left]
  · intro h
    congr 1
    funext n
    rw [binomialConv_altSeries_left, h n]

/-- The two generating-function equations are equivalent, which is binomial inversion. -/
theorem egfA_eq_exp_mul_iff_egfA_eq_altSeries_mul (a b : ℕ → A) :
    egfA A b = exp A * egfA A a ↔ egfA A a = altSeries A * egfA A b := by
  constructor
  · intro h
    rw [h, ← mul_assoc, mul_comm (altSeries A), exp_mul_altSeries, one_mul]
  · intro h
    rw [h, ← mul_assoc, exp_mul_altSeries, one_mul]

end InversionEGF

end Fabius
