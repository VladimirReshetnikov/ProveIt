import FabiusFunction.MeasureRefinement
import FabiusFunction.ThueMorseComplexProductBridge

/-!
# Uniform digit prefixes as finite Thue--Morse blocks

`MeasureRefinement.lean` constructs the law `uniformDigitPrefix m` of the
first `m` centred dyadic uniform digits and computes its characteristic
function as a finite sinc product.  Independently,
`ThueMorseComplexProductBridge.lean` identifies that same product with an
exact signed Thue--Morse exponential block.  This module supplies the missing
consumer bridge between the probability and arithmetic APIs.

The main equality is total: it holds at every level, including `m = 0`, and
at the origin.  The removable order-`m` zero remains visible on the
Thue--Morse side.  A quotient form solving for the characteristic function is
also recorded away from the origin.

## Main results

* `charFun_uniformDigitPrefix_eq_shiftedComplexSincPrefix` identifies the
  finite-prefix characteristic function with the canonical complex sinc
  prefix.
* `thueMorseBlock_cexp_eq_charFun_uniformDigitPrefix` is the denominator-free
  signed-block formula, valid without side conditions.
* `charFun_uniformDigitPrefix_eq_thueMorseBlock_cexp` is the corresponding
  quotient formula for a nonzero real frequency.
-/

set_option autoImplicit false

open Finset MeasureTheory

namespace Fabius

/-- The characteristic function of the first `m` centred dyadic uniform
digits is exactly the canonical finite complex sinc prefix.  This is the
probability-law bridge between `MeasureRefinement.lean` and the finite
Thue--Morse product calculus. -/
theorem charFun_uniformDigitPrefix_eq_shiftedComplexSincPrefix
    (m : ℕ) (t : ℝ) :
    charFun (uniformDigitPrefix m) t =
      shiftedComplexSincPrefix m (t : ℂ) := by
  rw [charFun_uniformDigitPrefix]
  unfold shiftedComplexSincPrefix
  refine Finset.prod_congr rfl fun k _ => ?_
  congr 1
  norm_cast

/-- The total signed Thue--Morse exponential block computes the
characteristic function of the first `m` centred dyadic uniform digits.  The
formula includes the empty level and the origin: no cancellation by the
frequency is used. -/
theorem thueMorseBlock_cexp_eq_charFun_uniformDigitPrefix
    (m : ℕ) (t : ℝ) :
    ∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
        Complex.exp (((2 * (t : ℂ) / (2 : ℂ) ^ m) * Complex.I)) ^ n =
      (-Complex.I) ^ m * (t : ℂ) ^ m /
          (2 : ℂ) ^ (Nat.choose m 2) *
        Complex.exp
          (Complex.I * (t : ℂ) * (1 - 1 / (2 : ℂ) ^ m)) *
        charFun (uniformDigitPrefix m) t := by
  rw [charFun_uniformDigitPrefix_eq_shiftedComplexSincPrefix]
  exact thueMorseBlock_cexp_eq_sincPrefix m (t : ℂ)

/-- Away from zero, the total finite-block identity can be solved for the
digit-prefix characteristic function. -/
theorem charFun_uniformDigitPrefix_eq_thueMorseBlock_cexp
    {m : ℕ} {t : ℝ} (ht : t ≠ 0) :
    charFun (uniformDigitPrefix m) t =
      Complex.I ^ m * (2 : ℂ) ^ (Nat.choose m 2) / (t : ℂ) ^ m *
        Complex.exp
          (-Complex.I * (t : ℂ) * (1 - 1 / (2 : ℂ) ^ m)) *
        (∑ n ∈ range (2 ^ m), (thueMorseSign n : ℂ) *
          Complex.exp (((2 * (t : ℂ) / (2 : ℂ) ^ m) * Complex.I)) ^ n) := by
  rw [charFun_uniformDigitPrefix_eq_shiftedComplexSincPrefix]
  exact shiftedComplexSincPrefix_eq_thueMorseBlock_cexp
    (m := m) (t := (t : ℂ)) (Complex.ofReal_ne_zero.mpr ht)

end Fabius
