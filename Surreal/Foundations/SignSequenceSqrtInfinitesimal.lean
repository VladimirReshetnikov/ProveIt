import Surreal.Foundations.SignSequenceRoots
import Surreal.Foundations.SignSequenceStandardPartTopology
import Surreal.Foundations.SignSequenceValuation

/-!
# Square roots of actual positive infinitesimals

The constructed square root preserves infinitesimality and halves the
leading exponent. These facts supply the square-root scale in
`trigonometry:prop:acosendpoint`.
-/

universe u

namespace Surreal.Foundations.SignSequence

/-- The nonnegative square root of a nonnegative infinitesimal is infinitesimal. -/
theorem infinitesimal_sqrt {x : SignSequence.{u}} (hx : 0 ≤ x) (hi : IsInfinitesimal x) :
    IsInfinitesimal (sqrt x) := by
  apply (isInfinitesimal_iff_forall_real_abs_lt _).mpr
  intro r hr
  have h := (isInfinitesimal_iff_forall_real_abs_lt x).mp hi (r ^ 2) (sq_pos_of_pos hr)
  rw [abs_of_nonneg hx, map_pow] at h
  rw [abs_of_nonneg (sqrt_nonneg x)]
  have hs := sqrt_sq hx
  have hp : (0 : SignSequence.{u}) < ofReal r := by
    simpa only [map_zero] using ofReal_strictMono hr
  nlinarith [sqrt_nonneg x]

/-- The square root halves the actual leading exponent at every positive scale. -/
theorem leadingExponent_sqrt {x : SignSequence.{u}} (hx : 0 < x) :
    leadingExponent (sqrt x) = leadingExponent x / 2 := by
  have h := congrArg leadingExponent (sqrt_sq hx.le)
  rw [leadingExponent_pow] at h
  norm_num at h
  linarith

/-- The actual square-root valuation is half the input's finite valuation exponent. -/
theorem valuation_sqrt {x : SignSequence.{u}} (hx : 0 < x) :
    valuation (sqrt x) = ((-leadingExponent x / 2 : SignSequence.{u}) : WithTop SignSequence.{u}) := by
  rw [valuation_of_ne_zero (sqrt_pos hx).ne', leadingExponent_sqrt hx]
  congr 1
  ring

end Surreal.Foundations.SignSequence
