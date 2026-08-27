import FabiusFunction.SaddleLogExpansionAlgebra

/-!
# Products and recursive logarithmic coefficients

This module records the finite coefficient algebra behind the familiar formal
identity `log (A * B) = log A + log B`.  The statements are phrased entirely
in terms of the recursive coefficient engines from
`SaddleLogExpansionAlgebra`; no convergence or analytic logarithm is involved.

The geometric-product theorem is the reusable endpoint: a coefficient identity
`q^n a_n = (a * b)_n` becomes
`(q^n - 1) log(a)_n = log(b)_n`.  It is the formal core of the centered
Rvachev cumulant calculation, but is independent of that application.
-/

set_option autoImplicit false

open scoped BigOperators
open Finset PowerSeries

namespace Fabius.SaddleExpansion

noncomputable section

variable {R : Type*}

/-- The Cauchy convolution of two coefficient families. -/
def coefficientConvolution [Semiring R] (a b : ℕ → R) (n : ℕ) : R :=
  ∑ ij ∈ antidiagonal n, a ij.1 * b ij.2

/-- The constant coefficient of a Cauchy convolution is the product of the
constant coefficients. -/
@[simp] theorem coefficientConvolution_zero [Semiring R] (a b : ℕ → R) :
    coefficientConvolution a b 0 = a 0 * b 0 := by
  simp [coefficientConvolution]

/-- Packaging a Cauchy convolution as a power series gives the product of the
packaged coefficient families. -/
theorem massSeries_coefficientConvolution [Semiring R] (a b : ℕ → R) :
    massSeries (coefficientConvolution a b) = massSeries a * massSeries b := by
  ext n
  simp [coefficientConvolution, PowerSeries.coeff_mul]

variable [CommRing R] [Algebra ℚ R]

/-- Formal logarithms turn Cauchy products of unit-constant families into
sums.  The proof uses the mutually inverse `expCoeff` and `logCoeff`
recurrences, so no convergence or analytic branch is involved. -/
theorem logCoeff_coefficientConvolution (a b : ℕ → R)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1) (n : ℕ) :
    logCoeff (coefficientConvolution a b) n = logCoeff a n + logCoeff b n := by
  let E : ℕ → R := fun j => logCoeff a j + logCoeff b j
  have hE0 : E 0 = 0 := by simp [E]
  have hexp : expCoeff E = coefficientConvolution a b := by
    funext j
    change expCoeff (fun k => logCoeff a k + logCoeff b k) j =
      coefficientConvolution a b j
    rw [expCoeff_add]
    simp_rw [expCoeff_logCoeff a ha0, expCoeff_logCoeff b hb0]
    rfl
  calc
    logCoeff (coefficientConvolution a b) n = logCoeff (expCoeff E) n := by
      rw [hexp]
    _ = E n := logCoeff_expCoeff E hE0 n
    _ = logCoeff a n + logCoeff b n := rfl

/-- The positive coefficients of a unit-constant family are reconstructed
from its logarithmic coefficients by the finite moment--cumulant recurrence. -/
theorem coefficient_succ_eq_logCoeff_sum (a : ℕ → R) (ha0 : a 0 = 1)
    (n : ℕ) :
    a (n + 1) = ((n + 1 : ℚ)⁻¹) •
      (∑ j ∈ range (n + 1),
        (j + 1 : R) * logCoeff a (j + 1) * a (n - j)) := by
  calc
    a (n + 1) = expCoeff (logCoeff a) (n + 1) :=
      (expCoeff_logCoeff a ha0 (n + 1)).symm
    _ = ((n + 1 : ℚ)⁻¹) •
        (∑ j ∈ range (n + 1),
          (j + 1 : R) * logCoeff a (j + 1) *
            expCoeff (logCoeff a) (n - j)) :=
      expCoeff_succ (logCoeff a) n
    _ = ((n + 1 : ℚ)⁻¹) •
        (∑ j ∈ range (n + 1),
          (j + 1 : R) * logCoeff a (j + 1) * a (n - j)) := by
      apply congrArg (fun z => ((n + 1 : ℚ)⁻¹) • z)
      apply Finset.sum_congr rfl
      intro j _hj
      rw [expCoeff_logCoeff a ha0]

/-- A geometric product equation
`q^n a_n = (a*b)_n` becomes the logarithmic coefficient equation
`(q^n-1) log(a)_n = log(b)_n`. -/
theorem logCoeff_geometric_product (q : R) (a b : ℕ → R)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hfunctional : ∀ j, q ^ j * a j = coefficientConvolution a b j)
    (n : ℕ) :
    (q ^ n - 1) * logCoeff a n = logCoeff b n := by
  have hlog :
      logCoeff (fun j => q ^ j * a j) n =
        logCoeff (coefficientConvolution a b) n := by
    apply logCoeff_congr n
    intro j _hj
    exact hfunctional j
  rw [logCoeff_rescale, logCoeff_coefficientConvolution a b ha0 hb0] at hlog
  calc
    (q ^ n - 1) * logCoeff a n =
        q ^ n * logCoeff a n - logCoeff a n := by ring
    _ = (logCoeff a n + logCoeff b n) - logCoeff a n := by rw [hlog]
    _ = logCoeff b n := by ring

end

end Fabius.SaddleExpansion
