import Mathlib.RingTheory.PowerSeries.Exp
import Mathlib.RingTheory.PowerSeries.Log
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Algebra.Module.Rat
import FabiusFunction.BellStirling

/-!
# Exponential generating functions of the Stirling triangles

Over any commutative `ℚ`-algebra `A`, with `egf A a = ∑_n a n X^n/n!` the
exponential generating function of a rational sequence:

* **second kind:** `(e^X - 1)^k = ∑_n k! S(n,k) X^n/n!`, proved by expanding
  `(e^X - 1)^k` binomially into the rescaled exponentials `e^{mX}` and
  reading off `∑_m (-1)^(k-m) C(k,m) m^n = k! S(n,k)`, the surjection
  formula;
* **first kind, unsigned:** `(-log(1-X))^k = ∑_n k! c(n,k) X^n/n!`, proved
  by the first-order equation `(1 - X) Y' = (k+1) Y_k` that both sides of the
  `(k+1)`-st identity satisfy, together with uniqueness of solutions
  (`(1 - X)` is a unit and a power series over a torsion-free ring is
  determined by its derivative and constant term);
* **first kind, signed:** `log(1+X)^k = ∑_n k! s(n,k) X^n/n!`, obtained from
  the unsigned identity by the substitution `X ↦ -X` (`PowerSeries.rescale`).

The divided forms `∑_n S(n,k) X^n/n! = (e^X-1)^k/k!` etc. are recorded as
corollaries.  `-log(1-X)` is introduced here as `negLogOneSub A`, the series
`∑_{n ≥ 1} X^n/n`, with derivative `1/(1-X) = ∑_n X^n`.

## Main results

* `egf`, `coeff_egf`.
* `exp_sub_one_pow`, `egf_stirlingSecond`.
* `negLogOneSub`, `derivative_negLogOneSub`,
  `one_sub_X_mul_derivative_negLogOneSub`,
  `eq_of_one_sub_X_mul_derivative_eq` (the uniqueness principle).
* `negLogOneSub_pow`, `egf_stirlingFirst`.
* `rescale_neg_one_negLogOneSub`, `log_pow`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

section EGF

variable (A : Type*) [CommRing A] [Algebra ℚ A]

/-- The exponential generating function `∑_n a n X^n / n!` of a rational
sequence, as a power series over a `ℚ`-algebra. -/
noncomputable def egf (a : ℕ → ℚ) : A⟦X⟧ :=
  PowerSeries.mk fun n => algebraMap ℚ A (a n / n.factorial)

/-- The `n`-th coefficient of `egf A a` is the image of `a n / n!` in `A`. -/
@[simp] theorem coeff_egf (a : ℕ → ℚ) (n : ℕ) :
    coeff n (egf A a) = algebraMap ℚ A (a n / n.factorial) :=
  coeff_mk _ _

/-! ### The second kind -/

/-- **Column generating function of the second kind:**
`(e^X - 1)^k = ∑_n k! S(n,k) X^n/n!`. -/
theorem exp_sub_one_pow (k : ℕ) :
    (exp A - 1) ^ k = egf A fun n => k.factorial * Nat.stirlingSecond n k := by
  ext n
  rw [coeff_egf, sub_pow, map_sum]
  have hterm : ∀ m ∈ Finset.range (k + 1),
      coeff n ((-1 : A⟦X⟧) ^ (m + k) * exp A ^ m * 1 ^ (k - m) * (k.choose m : A⟦X⟧))
        = ((-1) ^ (k - m) * (k.choose m : A) * (m : A) ^ n) *
            algebraMap ℚ A (1 / n.factorial) := by
    intro m hm
    have hmk : m ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hm)
    have hre : (-1 : A⟦X⟧) ^ (m + k) * exp A ^ m * 1 ^ (k - m) * (k.choose m : A⟦X⟧)
        = ((-1) ^ (k - m) * (k.choose m : A)) • exp A ^ m := by
      rw [smul_eq_C_mul, map_mul, map_pow, map_neg, map_one, map_natCast, one_pow, mul_one,
        neg_one_pow_sub_eq_neg_one_pow_add hmk, add_comm k m]
      ring
    rw [hre, coeff_smul, smul_eq_mul, exp_pow_eq_rescale_exp, coeff_rescale, coeff_exp]
    ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_mul]
  have hS : (∑ m ∈ Finset.range (k + 1), (-1 : A) ^ (k - m) * (k.choose m : A) * (m : A) ^ n)
      = algebraMap ℚ A (k.factorial * Nat.stirlingSecond n k) := by
    have h := congrArg (Int.cast : ℤ → A) (factorial_mul_stirlingSecond_eq_sum n k)
    push_cast at h
    rw [← h, map_mul, map_natCast, map_natCast]
  rw [hS, ← map_mul, mul_one_div]

/-- The divided form `∑_n S(n,k) X^n/n! = (e^X - 1)^k / k!`. -/
theorem egf_stirlingSecond (k : ℕ) :
    egf A (fun n => (Nat.stirlingSecond n k : ℚ)) =
      algebraMap ℚ A (1 / k.factorial) • (exp A - 1) ^ k := by
  rw [exp_sub_one_pow]
  ext n
  rw [coeff_smul, smul_eq_mul, coeff_egf, coeff_egf, ← map_mul]
  congr 1
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  try ring

/-! ### `-log(1 - X)` and the uniqueness principle -/

/-- The series `-log(1 - X) = ∑_{n ≥ 1} X^n / n`. -/
noncomputable def negLogOneSub : A⟦X⟧ :=
  PowerSeries.mk fun n => if n = 0 then 0 else algebraMap ℚ A (1 / n)

/-- The coefficient of `X^n` in `-log(1-X)` is zero at `n = 0` and `1/n` otherwise. -/
theorem coeff_negLogOneSub (n : ℕ) :
    coeff n (negLogOneSub A) = if n = 0 then 0 else algebraMap ℚ A (1 / n) :=
  coeff_mk _ _

/-- The series `-log(1-X)` has zero constant coefficient. -/
@[simp] theorem constantCoeff_negLogOneSub : constantCoeff (negLogOneSub A) = 0 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_negLogOneSub, if_pos rfl]

/-- `d/dX (-log(1-X)) = ∑_n X^n`. -/
theorem derivative_negLogOneSub : d⁄dX A (negLogOneSub A) = PowerSeries.mk 1 := by
  ext n
  rw [coeff_derivative, coeff_negLogOneSub, coeff_mk, if_neg (Nat.succ_ne_zero n), Pi.one_apply]
  have h1 : ((n : A) + 1) = algebraMap ℚ A ((n : ℚ) + 1) := by simp
  rw [h1, ← map_mul, Nat.cast_succ, one_div_mul_cancel (by positivity : ((n : ℚ) + 1) ≠ 0),
    map_one]

/-- `(1 - X) · d/dX (-log(1-X)) = 1`. -/
theorem one_sub_X_mul_derivative_negLogOneSub :
    (1 - X) * d⁄dX A (negLogOneSub A) = 1 := by
  rw [derivative_negLogOneSub, mul_comm, mk_one_mul_one_sub_eq_one]

/-- **Uniqueness principle:** two power series over a `ℚ`-algebra with the same
constant term and with `(1 - X) f' = (1 - X) g'` are equal. -/
theorem eq_of_one_sub_X_mul_derivative_eq {f g : A⟦X⟧}
    (hD : (1 - X) * d⁄dX A f = (1 - X) * d⁄dX A g)
    (hc : constantCoeff f = constantCoeff g) : f = g := by
  haveI : IsAddTorsionFree A := IsAddTorsionFree.of_module_rat A
  apply derivative.ext _ hc
  have h := congrArg (fun p : A⟦X⟧ => PowerSeries.mk 1 * p) hD
  simp only [← mul_assoc, mk_one_mul_one_sub_eq_one, one_mul] at h
  exact h

/-! ### The first kind, unsigned -/

/-- The first-order equation satisfied by the first-kind column series:
`(1 - X) · d/dX (∑_n (k+1)! c(n,k+1) X^n/n!) = (k+1) · ∑_n k! c(n,k) X^n/n!`. -/
theorem one_sub_X_mul_derivative_egf_stirlingFirst (k : ℕ) :
    (1 - X) * d⁄dX A (egf A fun n => (k + 1).factorial * Nat.stirlingFirst n (k + 1)) =
      ((k + 1 : ℕ) : A⟦X⟧) * egf A fun n => k.factorial * Nat.stirlingFirst n k := by
  ext n
  have hcast : ∀ m : ℕ, ((m : A) + 1) = algebraMap ℚ A ((m : ℚ) + 1) := by
    intro m
    simp
  have hk : ((k + 1 : ℕ) : A) = algebraMap ℚ A ((k + 1 : ℕ) : ℚ) := by simp
  rw [sub_mul, one_mul, map_sub, ← map_natCast (C : A →+* A⟦X⟧) (k + 1), coeff_C_mul, hk,
    coeff_egf, coeff_derivative, coeff_egf, hcast]
  cases n with
  | zero =>
    rw [coeff_zero_X_mul, sub_zero, ← map_mul, ← map_mul]
    congr 1
    rw [Nat.stirlingFirst_succ_succ, Nat.factorial_succ k]
    push_cast
    ring
  | succ n =>
    rw [coeff_succ_X_mul, coeff_derivative, coeff_egf, hcast, ← map_mul, ← map_mul, ← map_sub,
      ← map_mul]
    congr 1
    rw [Nat.stirlingFirst_succ_succ, Nat.factorial_succ (n + 1), Nat.factorial_succ k]
    have h1 : ((n + 1).factorial : ℚ) ≠ 0 := by positivity
    push_cast
    field_simp
    try ring

/-- **Column generating function of the first kind (unsigned):**
`(-log(1-X))^k = ∑_n k! c(n,k) X^n/n!`. -/
theorem negLogOneSub_pow (k : ℕ) :
    negLogOneSub A ^ k = egf A fun n => k.factorial * Nat.stirlingFirst n k := by
  induction k with
  | zero =>
    ext n
    rw [pow_zero, coeff_one, coeff_egf]
    cases n with
    | zero => simp
    | succ n => simp
  | succ k ih =>
    apply eq_of_one_sub_X_mul_derivative_eq
    · rw [one_sub_X_mul_derivative_egf_stirlingFirst, derivative_pow, Nat.add_sub_cancel, ih]
      calc (1 - X : A⟦X⟧) * (((k + 1 : ℕ) : A⟦X⟧) *
              (egf A fun n => k.factorial * Nat.stirlingFirst n k) * d⁄dX A (negLogOneSub A))
          = ((k + 1 : ℕ) : A⟦X⟧) * (egf A fun n => k.factorial * Nat.stirlingFirst n k) *
              ((1 - X) * d⁄dX A (negLogOneSub A)) := by ring
        _ = _ := by rw [one_sub_X_mul_derivative_negLogOneSub, mul_one]
    · rw [map_pow, constantCoeff_negLogOneSub, zero_pow (Nat.succ_ne_zero k),
        ← coeff_zero_eq_constantCoeff_apply, coeff_egf]
      simp

/-- The divided form `∑_n c(n,k) X^n/n! = (-log(1-X))^k / k!`. -/
theorem egf_stirlingFirst (k : ℕ) :
    egf A (fun n => (Nat.stirlingFirst n k : ℚ)) =
      algebraMap ℚ A (1 / k.factorial) • negLogOneSub A ^ k := by
  rw [negLogOneSub_pow]
  ext n
  rw [coeff_smul, smul_eq_mul, coeff_egf, coeff_egf, ← map_mul]
  congr 1
  have hk : (k.factorial : ℚ) ≠ 0 := by positivity
  field_simp
  try ring

/-! ### The first kind, signed -/

/-- Under `X ↦ -X`, `-log(1-X)` becomes `-log(1+X)`. -/
theorem rescale_neg_one_negLogOneSub : rescale (-1 : A) (negLogOneSub A) = -log A := by
  ext n
  rw [coeff_rescale, coeff_negLogOneSub, map_neg, coeff_log]
  split_ifs with h
  · simp
  · have h1 : ((-1 : A) ^ n) = algebraMap ℚ A ((-1 : ℚ) ^ n) := by simp
    rw [h1, ← map_mul, ← map_neg]
    congr 1
    ring

/-- **Column generating function of the first kind (signed):**
`log(1+X)^k = ∑_n k! s(n,k) X^n/n!`. -/
theorem log_pow (k : ℕ) :
    log A ^ k = egf A fun n => k.factorial * signedStirlingFirst n k := by
  have h := congrArg (rescale (-1 : A)) (negLogOneSub_pow A k)
  rw [map_pow, rescale_neg_one_negLogOneSub, neg_pow] at h
  -- h : (-1)^k * log A ^ k = rescale (-1) (egf (k! c))
  have hk : ((-1 : A⟦X⟧) ^ k) * ((-1 : A⟦X⟧) ^ k) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  calc log A ^ k = ((-1 : A⟦X⟧) ^ k * (-1) ^ k) * log A ^ k := by rw [hk, one_mul]
    _ = (-1 : A⟦X⟧) ^ k * rescale (-1 : A) (egf A fun n => k.factorial * Nat.stirlingFirst n k) := by
        rw [mul_assoc, h]
    _ = egf A fun n => k.factorial * signedStirlingFirst n k := by
        ext n
        have hC : ((-1 : A⟦X⟧) ^ k) = C ((-1 : A) ^ k) := by simp
        rw [hC, coeff_C_mul, coeff_rescale, coeff_egf, coeff_egf]
        have h1 : ((-1 : A) ^ k) = algebraMap ℚ A ((-1 : ℚ) ^ k) := by simp
        have h2 : ((-1 : A) ^ n) = algebraMap ℚ A ((-1 : ℚ) ^ n) := by simp
        rw [h1, h2, ← map_mul, ← map_mul]
        congr 1
        unfold signedStirlingFirst
        rcases le_or_gt k n with hkn | hkn
        · push_cast
          rw [neg_one_pow_sub_eq_neg_one_pow_add hkn]
          ring
        · rw [Nat.stirlingFirst_eq_zero_of_lt hkn]
          simp

end EGF

end Fabius
