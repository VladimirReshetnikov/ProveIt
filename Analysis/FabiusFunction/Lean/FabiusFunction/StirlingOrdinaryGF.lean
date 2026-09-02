import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Column ordinary generating functions of the Stirling numbers of the second kind

For fixed `k`, the ordinary generating function of the `k`-th column of the
Stirling triangle of the second kind is a rational function:

`∑_{r ≥ 0} S(k + r, k) x^r = ∏_{j = 1}^{k} 1/(1 - j x)`.

We state this in `R⟦X⟧` for any commutative ring `R` as the identity

`(∏_{j < k} (1 - (j + 1) X)) · ∑_r S(k + r, k) X^r = 1`,

which follows from the recurrence `S(n+1, k+1) = (k+1) S(n, k+1) + S(n, k)` in
the form `(1 - (k+1) X) · F_{k+1} = F_k`.

## Main results

* `stirlingColumnOGF`: the column series `F_k = ∑_r S(k + r, k) X^r`.
* `one_sub_mul_X_mul_stirlingColumnOGF_succ`: `(1 - (k+1) X) F_{k+1} = F_k`.
* `prod_one_sub_mul_X_mul_stirlingColumnOGF`: `(∏_{j<k} (1 - (j+1) X)) F_k = 1`.
* `stirlingColumnOGF_mul_prod_one_sub_mul_X`, `isUnit_stirlingColumnOGF`.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius

variable (R : Type*) [CommRing R]

/-- The ordinary generating function `∑_{r ≥ 0} S(k + r, k) X^r` of the `k`-th
column of the Stirling numbers of the second kind. -/
noncomputable def stirlingColumnOGF (k : ℕ) : R⟦X⟧ :=
  PowerSeries.mk fun r => (Nat.stirlingSecond (k + r) k : R)

/-- The coefficients of the column series. -/
@[simp]
theorem coeff_stirlingColumnOGF (k r : ℕ) :
    PowerSeries.coeff r (stirlingColumnOGF R k) = (Nat.stirlingSecond (k + r) k : R) := by
  rw [stirlingColumnOGF, coeff_mk]

/-- The zeroth column series is `1`. -/
theorem stirlingColumnOGF_zero : stirlingColumnOGF R 0 = 1 := by
  ext r
  rw [coeff_stirlingColumnOGF, PowerSeries.coeff_one]
  cases r with
  | zero => simp
  | succ r => simp [Nat.stirlingSecond_succ_zero]

/-- The column recurrence `(1 - (k+1) X) · F_{k+1} = F_k`, the generating-function
form of `S(n+1, k+1) = (k+1) S(n, k+1) + S(n, k)`. -/
theorem one_sub_mul_X_mul_stirlingColumnOGF_succ (k : ℕ) :
    (1 - ((k + 1 : ℕ) : R⟦X⟧) * X) * stirlingColumnOGF R (k + 1) = stirlingColumnOGF R k := by
  have hform : (1 - ((k + 1 : ℕ) : R⟦X⟧) * X) * stirlingColumnOGF R (k + 1)
      = stirlingColumnOGF R (k + 1)
        - PowerSeries.C ((k + 1 : ℕ) : R) * (X * stirlingColumnOGF R (k + 1)) := by
    rw [map_natCast (PowerSeries.C : R →+* R⟦X⟧) (k + 1)]
    ring
  rw [hform]
  ext r
  rw [map_sub, coeff_C_mul, coeff_stirlingColumnOGF, coeff_stirlingColumnOGF]
  cases r with
  | zero =>
    simp [Nat.stirlingSecond_self]
  | succ r =>
    rw [coeff_succ_X_mul, coeff_stirlingColumnOGF]
    have h := Nat.stirlingSecond_succ_succ (k + r + 1) k
    rw [show k + 1 + (r + 1) = k + r + 1 + 1 by omega, show k + 1 + r = k + r + 1 by omega,
      show k + (r + 1) = k + r + 1 by omega, h]
    push_cast
    ring

/-- **Column generating function of the Stirling numbers of the second kind:**
`(∏_{j < k} (1 - (j+1) X)) · ∑_r S(k + r, k) X^r = 1`, i.e.
`∑_r S(k + r, k) X^r = ∏_{j=1}^{k} 1/(1 - j X)`. -/
theorem prod_one_sub_mul_X_mul_stirlingColumnOGF (k : ℕ) :
    (∏ j ∈ Finset.range k, (1 - ((j + 1 : ℕ) : R⟦X⟧) * X)) * stirlingColumnOGF R k = 1 := by
  induction k with
  | zero => simp [stirlingColumnOGF_zero]
  | succ k ih =>
    rw [Finset.prod_range_succ, mul_assoc, one_sub_mul_X_mul_stirlingColumnOGF_succ, ih]

/-- The commuted form of `prod_one_sub_mul_X_mul_stirlingColumnOGF`. -/
theorem stirlingColumnOGF_mul_prod_one_sub_mul_X (k : ℕ) :
    stirlingColumnOGF R k * (∏ j ∈ Finset.range k, (1 - ((j + 1 : ℕ) : R⟦X⟧) * X)) = 1 := by
  rw [mul_comm]
  exact prod_one_sub_mul_X_mul_stirlingColumnOGF R k

/-- The column series is a unit of `R⟦X⟧`, with inverse `∏_{j<k} (1 - (j+1) X)`. -/
theorem isUnit_stirlingColumnOGF (k : ℕ) : IsUnit (stirlingColumnOGF R k) :=
  IsUnit.of_mul_eq_one _ (stirlingColumnOGF_mul_prod_one_sub_mul_X R k)

/-- The column series is the product of the geometric series `∑_r (j+1)^r X^r`,
`j < k`: `∑_r S(k+r,k) X^r = ∏_{j<k} ∑_r (j+1)^r X^r`. -/
theorem stirlingColumnOGF_eq_prod_mk_pow (k : ℕ) :
    stirlingColumnOGF R k =
      ∏ j ∈ Finset.range k, PowerSeries.mk (fun r => ((j + 1 : ℕ) : R) ^ r) := by
  have hgeom : ∀ j : ℕ, (1 - ((j + 1 : ℕ) : R⟦X⟧) * X) *
      PowerSeries.mk (fun r => ((j + 1 : ℕ) : R) ^ r) = 1 := by
    intro j
    have hform : (1 - ((j + 1 : ℕ) : R⟦X⟧) * X) * PowerSeries.mk (fun r => ((j + 1 : ℕ) : R) ^ r)
        = PowerSeries.mk (fun r => ((j + 1 : ℕ) : R) ^ r)
          - PowerSeries.C ((j + 1 : ℕ) : R) * (X * PowerSeries.mk (fun r => ((j + 1 : ℕ) : R) ^ r)) := by
      rw [map_natCast (PowerSeries.C : R →+* R⟦X⟧) (j + 1)]
      ring
    rw [hform]
    ext r
    rw [map_sub, coeff_C_mul, coeff_mk, PowerSeries.coeff_one]
    cases r with
    | zero => simp
    | succ r =>
      rw [coeff_succ_X_mul, coeff_mk]
      simp [pow_succ]
      ring
  have hprod : (∏ j ∈ Finset.range k, (1 - ((j + 1 : ℕ) : R⟦X⟧) * X)) *
      ∏ j ∈ Finset.range k, PowerSeries.mk (fun r => ((j + 1 : ℕ) : R) ^ r) = 1 := by
    rw [← Finset.prod_mul_distrib]
    exact Finset.prod_eq_one fun j _ => hgeom j
  have hu := prod_one_sub_mul_X_mul_stirlingColumnOGF R k
  -- both are inverses of the same element
  calc stirlingColumnOGF R k
      = stirlingColumnOGF R k * ((∏ j ∈ Finset.range k, (1 - ((j + 1 : ℕ) : R⟦X⟧) * X)) *
          ∏ j ∈ Finset.range k, PowerSeries.mk (fun r => ((j + 1 : ℕ) : R) ^ r)) := by
        rw [hprod, mul_one]
    _ = (stirlingColumnOGF R k * ∏ j ∈ Finset.range k, (1 - ((j + 1 : ℕ) : R⟦X⟧) * X)) *
          ∏ j ∈ Finset.range k, PowerSeries.mk (fun r => ((j + 1 : ℕ) : R) ^ r) := by ring
    _ = _ := by rw [mul_comm (stirlingColumnOGF R k), hu, one_mul]

end Fabius
