import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# The Catalan generating function

Mathlib defines the Catalan numbers by the first-return recurrence
`C_{n+1} = ∑_{i+j=n} C_i C_j` and proves `C_n = C(2n,n)/(n+1)` (`catalan_eq_centralBinom_div`)
and that they count Dyck words (`DyckWord.card_dyckWord_semilength_eq_catalan`).  Here we record
the generating-function form of the recurrence, `C(z) = 1 + z C(z)^2` (`catalanSeries_eq`), its
uniqueness among power series (`eq_catalanSeries_of_eq_one_add_X_mul_sq`: the constant term `1`
singles out the branch), and the reflection form `C_{n+1} = C(2n+2,n+1) - C(2n+2,n)`
(`catalan_succ_eq_choose_sub_choose`).

## Main results

* `catalanSeries`, `coeff_catalanSeries`, `catalanSeries_eq`,
  `eq_catalanSeries_of_eq_one_add_X_mul_sq`.
* `catalan_succ_eq_choose_sub_choose`.
-/

set_option autoImplicit false

open PowerSeries Finset

namespace Fabius

section Series

variable (R : Type*) [CommRing R]

/-- The Catalan generating function `C(z) = ∑_n C_n z^n`. -/
noncomputable def catalanSeries : R⟦X⟧ := PowerSeries.mk fun n => (catalan n : R)

/-- The coefficient of `zⁿ` in the Catalan series is the `n`-th Catalan number. -/
@[simp] theorem coeff_catalanSeries (n : ℕ) :
    PowerSeries.coeff n (catalanSeries R) = (catalan n : R) := by
  rw [catalanSeries, coeff_mk]

/-- **The first-return equation:** `C(z) = 1 + z C(z)^2`. -/
theorem catalanSeries_eq : catalanSeries R = 1 + X * catalanSeries R ^ 2 := by
  ext n
  cases n with
  | zero =>
    rw [coeff_catalanSeries, map_add, coeff_zero_X_mul, add_zero, PowerSeries.coeff_one,
      if_pos rfl, catalan_zero, Nat.cast_one]
  | succ n =>
    rw [coeff_catalanSeries, map_add, coeff_succ_X_mul, sq, PowerSeries.coeff_mul,
      PowerSeries.coeff_one, if_neg (Nat.succ_ne_zero n), zero_add, catalan_succ', Nat.cast_sum]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [coeff_catalanSeries, coeff_catalanSeries, Nat.cast_mul]

/-- **Uniqueness:** a power series `F` with `F = 1 + z F^2` is the Catalan series
(the constant term `1` singles out the branch). -/
theorem eq_catalanSeries_of_eq_one_add_X_mul_sq (F : R⟦X⟧) (hF : F = 1 + X * F ^ 2) :
    F = catalanSeries R := by
  ext n
  refine Nat.strong_induction_on n ?_
  intro n ih
  cases n with
  | zero =>
    have h := congrArg (PowerSeries.coeff 0) hF
    rw [map_add, coeff_zero_X_mul, add_zero, PowerSeries.coeff_one, if_pos rfl] at h
    rw [h, coeff_catalanSeries, catalan_zero, Nat.cast_one]
  | succ n =>
    have h := congrArg (PowerSeries.coeff (n + 1)) hF
    rw [map_add, coeff_succ_X_mul, sq, PowerSeries.coeff_mul, PowerSeries.coeff_one,
      if_neg (Nat.succ_ne_zero n), zero_add] at h
    rw [h, coeff_catalanSeries, catalan_succ', Nat.cast_sum]
    refine Finset.sum_congr rfl fun p hp => ?_
    have hp' := Finset.mem_antidiagonal.mp hp
    rw [ih p.1 (by omega), ih p.2 (by omega), coeff_catalanSeries, coeff_catalanSeries,
      Nat.cast_mul]

end Series

/-- **The reflection form of the Catalan formula:**
`C_{n+1} = C(2n+2, n+1) - C(2n+2, n)`. -/
theorem catalan_succ_eq_choose_sub_choose (n : ℕ) :
    catalan (n + 1) = (2 * (n + 1)).choose (n + 1) - (2 * (n + 1)).choose n := by
  have hc := succ_mul_catalan_eq_centralBinom (n + 1)
  rw [Nat.centralBinom_eq_two_mul_choose] at hc
  have hr := Nat.choose_succ_right_eq (2 * (n + 1)) n
  rw [show 2 * (n + 1) - n = n + 2 by omega] at hr
  have h : (n + 1 + 1) * (catalan (n + 1) + (2 * (n + 1)).choose n) =
      (n + 1 + 1) * (2 * (n + 1)).choose (n + 1) := by
    nlinarith [hc, hr]
  exact Nat.eq_sub_of_add_eq (Nat.eq_of_mul_eq_mul_left (Nat.succ_pos (n + 1)) h)

end Fabius
