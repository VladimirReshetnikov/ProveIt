import FabiusFunction.SaddleLogExpansionAlgebra

/-!
# The formal logarithm turns products into sums

`SaddleLogExpansionAlgebra` builds the formal logarithm of a series with
unit constant term as a coefficient recurrence.  This file proves the
one structural property that makes it a *logarithm*:

`log (A·B) = log A + log B`,

and its finite-product form `log (∏ F i) = ∑ log (F i)`.

Two deliberate choices of generality:

* the statement is about **power series**, not coefficient families —
  `logOf C` is the logarithm of `C` itself — so the finite-product form
  is an ordinary `Finset` induction rather than an `n`-fold Cauchy
  convolution;
* the ring is an arbitrary commutative `ℚ`-algebra.  Nothing here is
  analytic: no convergence, no ordering, no field.  The frontier
  reports use "log of a product is a sum of logs" analytically on
  convergent sinc products in several separate proofs; the fact they
  are using is purely formal and is proved once here.

The proof is the uniqueness principle of the recurrence: `log A + log B`
has vanishing constant term and satisfies the defining differential
equation `(AB)·Y′ = (AB)′` of `log (AB)`, because Leibniz splits `(AB)′`
into exactly the two pieces `A·(B·log B ′)` and `B·(A·log A ′)`.

* `logOf` — the logarithm of a power series.
* `logOf_mul` — **the product rule**.
* `logOf_prod` — the finite-product form.
-/

set_option autoImplicit false

open Finset PowerSeries

namespace Fabius.SaddleExpansion

variable {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The formal logarithm of a power series with unit constant term,
packaged as an operation on series rather than on coefficient
families. -/
noncomputable def logOf (C : PowerSeries R) : PowerSeries R :=
  logSeries (fun n => PowerSeries.coeff n C)

/-- `massSeries` is a left inverse of taking coefficients. -/
omit [Algebra ℚ R] in
@[simp] theorem massSeries_coeff (C : PowerSeries R) :
    massSeries (fun n => PowerSeries.coeff n C) = C := by
  ext n
  rw [coeff_massSeries]

@[simp] theorem constantCoeff_logOf (C : PowerSeries R) :
    PowerSeries.constantCoeff (logOf C) = 0 := by
  rw [logOf, constantCoeff_logSeries]

/-- The defining differential equation, restated for `logOf`. -/
theorem mul_derivative_logOf {C : PowerSeries R}
    (hC : PowerSeries.constantCoeff C = 1) :
    C * d⁄dX R (logOf C) = d⁄dX R C := by
  have h0 : (fun n => PowerSeries.coeff n C) 0 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hC
    exact hC
  have h := massSeries_mul_derivative_logSeries
    (fun n => PowerSeries.coeff n C) h0
  rw [massSeries_coeff] at h
  exact h

/-- `logOf` is determined by the differential equation and the
normalization. -/
theorem logOf_eq_of {C B : PowerSeries R}
    (hC : PowerSeries.constantCoeff C = 1)
    (hderiv : C * d⁄dX R B = d⁄dX R C)
    (hzero : PowerSeries.constantCoeff B = 0) :
    B = logOf C := by
  have h0 : (fun n => PowerSeries.coeff n C) 0 = 1 := by
    rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply] at hC
    exact hC
  refine logSeries_unique _ h0 ?_ hzero
  rwa [massSeries_coeff]

/-- **The product rule**: `log (A·B) = log A + log B`. -/
theorem logOf_mul {A B : PowerSeries R}
    (hA : PowerSeries.constantCoeff A = 1)
    (hB : PowerSeries.constantCoeff B = 1) :
    logOf (A * B) = logOf A + logOf B := by
  have hAB : PowerSeries.constantCoeff (A * B) = 1 := by
    rw [map_mul, hA, hB, one_mul]
  symm
  refine logOf_eq_of hAB ?_ (by simp)
  rw [map_add]
  calc A * B * (d⁄dX R (logOf A) + d⁄dX R (logOf B))
      = B * (A * d⁄dX R (logOf A)) + A * (B * d⁄dX R (logOf B)) := by
        ring
    _ = B * d⁄dX R A + A * d⁄dX R B := by
        rw [mul_derivative_logOf hA, mul_derivative_logOf hB]
    _ = d⁄dX R (A * B) := by
        rw [Derivation.leibniz]
        simp only [smul_eq_mul]
        ring

/-- The logarithm of the unit series vanishes. -/
@[simp] theorem logOf_one : logOf (1 : PowerSeries R) = 0 := by
  symm
  refine logOf_eq_of (by simp) ?_ (by simp)
  simp

/-- **The finite-product form**: `log (∏ F i) = ∑ log (F i)`. -/
theorem logOf_prod {ι : Type*} (s : Finset ι) (F : ι → PowerSeries R)
    (hF : ∀ i ∈ s, PowerSeries.constantCoeff (F i) = 1) :
    logOf (∏ i ∈ s, F i) = ∑ i ∈ s, logOf (F i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
      have hFi : PowerSeries.constantCoeff (F i) = 1 :=
        hF i (Finset.mem_insert_self i s)
      have hrest : ∀ j ∈ s, PowerSeries.constantCoeff (F j) = 1 :=
        fun j hj => hF j (Finset.mem_insert_of_mem hj)
      have hprod : PowerSeries.constantCoeff (∏ j ∈ s, F j) = 1 := by
        rw [map_prod]
        exact Finset.prod_eq_one hrest
      rw [Finset.prod_insert hi, Finset.sum_insert hi,
        logOf_mul hFi hprod, ih hrest]

end Fabius.SaddleExpansion
