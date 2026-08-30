import FabiusFunction.CompleteHomogeneous
import Mathlib.RingTheory.PowerSeries.Inverse

/-!
# Generating series for complete homogeneous symmetric polynomials

This module packages the evaluated complete homogeneous symmetric polynomials
as a formal power series.  Adjoining one variable gives a geometric-series
recurrence, and iterating its denominator-cleared form proves the finite
product identity

`prod i in s, (1 - C (a i) * X) * sum n, h_n(a | s) X^n = 1`.

Everything is purely formal.  The coefficient and adjoining recurrences hold
over a commutative semiring.  Subtraction is used only for the cleared
denominators, and `PowerSeries.invOfUnit` gives their canonical reciprocal
over an arbitrary commutative ring, without a field or domain hypothesis.

## Main results

* `completeHomogeneousGeneratingSeriesOn_insert` is the adjoining-variable
  recurrence.
* `one_sub_mul_completeHomogeneousGeneratingSeriesOn_insert` clears its one
  linear denominator.
* `prod_one_sub_mul_completeHomogeneousGeneratingSeriesOn` clears all finite
  linear denominators.
* `completeHomogeneousGeneratingSeriesOn_eq_invOfUnit_prod` identifies the
  series with Mathlib's canonical inverse of that product.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

noncomputable section

/-- The ordinary formal generating series of the complete homogeneous
evaluations on the finite family indexed by `s`. -/
def completeHomogeneousGeneratingSeriesOn
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) : PowerSeries R :=
  PowerSeries.mk fun n ↦ completeHomogeneousEvalOn s a n

/-- The coefficient of the complete homogeneous generating series is the
corresponding complete homogeneous evaluation. -/
@[simp]
theorem coeff_completeHomogeneousGeneratingSeriesOn
    {R ι : Type*} [CommSemiring R]
    (s : Finset ι) (a : ι → R) (n : ℕ) :
    PowerSeries.coeff n (completeHomogeneousGeneratingSeriesOn s a) =
      completeHomogeneousEvalOn s a n := by
  rw [completeHomogeneousGeneratingSeriesOn, PowerSeries.coeff_mk]

/-- With no variables, the complete homogeneous generating series is one. -/
@[simp]
theorem completeHomogeneousGeneratingSeriesOn_empty
    {R ι : Type*} [CommSemiring R] (a : ι → R) :
    completeHomogeneousGeneratingSeriesOn (∅ : Finset ι) a = 1 := by
  ext n
  cases n with
  | zero =>
      simp [completeHomogeneousGeneratingSeriesOn,
        completeHomogeneousEvalOn]
  | succ n =>
      simp [completeHomogeneousEvalOn]

/-- Adjoining one variable gives the formal geometric-series recurrence

`H_(insert i s) = C(a i) * X * H_(insert i s) + H_s`.

The identity requires no subtraction and therefore holds over every
commutative semiring. -/
theorem completeHomogeneousGeneratingSeriesOn_insert
    {R ι : Type*} [CommSemiring R] [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∉ s) (a : ι → R) :
    completeHomogeneousGeneratingSeriesOn (insert i s) a =
      PowerSeries.C (a i) *
          (PowerSeries.X *
            completeHomogeneousGeneratingSeriesOn (insert i s) a) +
        completeHomogeneousGeneratingSeriesOn s a := by
  ext n
  cases n with
  | zero =>
      simp [completeHomogeneousGeneratingSeriesOn,
        completeHomogeneousEvalOn]
  | succ n =>
      simpa only [map_add,
        coeff_completeHomogeneousGeneratingSeriesOn,
        PowerSeries.coeff_C_mul, PowerSeries.coeff_succ_X_mul] using
        completeHomogeneousEvalOn_insert_succ hi a n

/-- Clearing the one-variable recurrence gives its linear-factor identity. -/
theorem one_sub_mul_completeHomogeneousGeneratingSeriesOn_insert
    {R ι : Type*} [CommRing R] [DecidableEq ι]
    {s : Finset ι} {i : ι} (hi : i ∉ s) (a : ι → R) :
    (1 - PowerSeries.C (a i) * PowerSeries.X) *
        completeHomogeneousGeneratingSeriesOn (insert i s) a =
      completeHomogeneousGeneratingSeriesOn s a := by
  calc
    (1 - PowerSeries.C (a i) * PowerSeries.X) *
        completeHomogeneousGeneratingSeriesOn (insert i s) a =
        completeHomogeneousGeneratingSeriesOn (insert i s) a -
          PowerSeries.C (a i) *
            (PowerSeries.X *
              completeHomogeneousGeneratingSeriesOn (insert i s) a) := by
          ring
    _ = completeHomogeneousGeneratingSeriesOn s a := by
      apply sub_eq_iff_eq_add.mpr
      calc
        completeHomogeneousGeneratingSeriesOn (insert i s) a =
            PowerSeries.C (a i) *
                (PowerSeries.X *
                  completeHomogeneousGeneratingSeriesOn (insert i s) a) +
              completeHomogeneousGeneratingSeriesOn s a :=
          completeHomogeneousGeneratingSeriesOn_insert hi a
        _ = completeHomogeneousGeneratingSeriesOn s a +
            PowerSeries.C (a i) *
              (PowerSeries.X *
                completeHomogeneousGeneratingSeriesOn (insert i s) a) := by
          ac_rfl

/-- The product of all finite linear denominators clears the complete
homogeneous generating series. -/
theorem prod_one_sub_mul_completeHomogeneousGeneratingSeriesOn
    {R ι : Type*} [CommRing R] (s : Finset ι) (a : ι → R) :
    (∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X)) *
        completeHomogeneousGeneratingSeriesOn s a = 1 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.prod_insert hi]
      calc
        ((1 - PowerSeries.C (a i) * PowerSeries.X) *
            ∏ j ∈ s, (1 - PowerSeries.C (a j) * PowerSeries.X)) *
              completeHomogeneousGeneratingSeriesOn (insert i s) a =
            (∏ j ∈ s,
                (1 - PowerSeries.C (a j) * PowerSeries.X)) *
              ((1 - PowerSeries.C (a i) * PowerSeries.X) *
                completeHomogeneousGeneratingSeriesOn (insert i s) a) := by
          ac_rfl
        _ = (∏ j ∈ s,
              (1 - PowerSeries.C (a j) * PowerSeries.X)) *
                completeHomogeneousGeneratingSeriesOn s a := by
          rw [one_sub_mul_completeHomogeneousGeneratingSeriesOn_insert hi a]
        _ = 1 := ih

/-- The complete homogeneous generating series is Mathlib's canonical formal
inverse of the product of its linear denominators.  This remains valid over a
commutative ring with zero divisors because the denominator has unit constant
coefficient and no cancellation argument is used. -/
theorem completeHomogeneousGeneratingSeriesOn_eq_invOfUnit_prod
    {R ι : Type*} [CommRing R] (s : Finset ι) (a : ι → R) :
    completeHomogeneousGeneratingSeriesOn s a =
      PowerSeries.invOfUnit
        (∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X))
        (1 : Rˣ) := by
  let D : PowerSeries R :=
    ∏ i ∈ s, (1 - PowerSeries.C (a i) * PowerSeries.X)
  have hD : D * completeHomogeneousGeneratingSeriesOn s a = 1 := by
    exact prod_one_sub_mul_completeHomogeneousGeneratingSeriesOn s a
  have hconstant : PowerSeries.constantCoeff D = ((1 : Rˣ) : R) := by
    simp [D]
  change completeHomogeneousGeneratingSeriesOn s a =
    PowerSeries.invOfUnit D (1 : Rˣ)
  calc
    completeHomogeneousGeneratingSeriesOn s a =
        1 * completeHomogeneousGeneratingSeriesOn s a := by rw [one_mul]
    _ = (PowerSeries.invOfUnit D (1 : Rˣ) * D) *
        completeHomogeneousGeneratingSeriesOn s a := by
      rw [PowerSeries.invOfUnit_mul D (1 : Rˣ) hconstant]
    _ = PowerSeries.invOfUnit D (1 : Rˣ) *
        (D * completeHomogeneousGeneratingSeriesOn s a) := by
      rw [mul_assoc]
    _ = PowerSeries.invOfUnit D (1 : Rˣ) := by rw [hD, mul_one]

end

end Fabius
