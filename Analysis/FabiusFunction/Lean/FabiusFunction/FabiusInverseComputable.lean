import FabiusFunction.EffectiveMonotoneInverse
import FabiusFunction.FabiusComputableSpline
import FabiusFunction.FabiusInverseLogarithmicModulus

/-!
# Computability of the inverse Fabius function

The computable centered-spline evaluator for `fabiusReal`, the explicit
inverse modulus, and tolerant monotone bisection together give a uniform
dyadic realizer for the inverse on `[0,1]`.  Clamping input names extends that
realizer to the total inverse, and the logarithmic Delta modulus supplies the
effective-uniform-continuity clause.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- Clamping the argument to `[0,1]` does not change the total inverse Fabius function. -/
theorem fabiusInv_unitClamp
    (F : BoundedFabius) (hF : IsFabius F) (x : ℝ) :
    fabiusInv F hF (unitClamp x) = fabiusInv F hF x := by
  by_cases hx0 : x ≤ 0
  · rw [unitClamp_eq_zero_of_nonpos hx0, fabiusInv_zero,
      fabiusInv_eq_zero_of_nonpos F hF hx0]
  by_cases hx1 : 1 ≤ x
  · rw [unitClamp_eq_one_of_one_le hx1, fabiusInv_one,
      fabiusInv_eq_one_of_one_le F hF hx1]
  · rw [unitClamp_of_mem ⟨le_of_not_ge hx0, le_of_not_ge hx1⟩]

private theorem fabiusInv_sequentiallyComputableOn_Icc
    (F : BoundedFabius) (hF : IsFabius F) :
    SequentiallyComputableOn (fabiusInv F hF) (Icc (0 : ℝ) 1) := by
  apply effectiveInversionOn_Icc
    (fabiusHasComputableDyadicApproximation F hF)
    (strictMonoOn_fabiusReal F hF)
    (den := inverseFabiusDeltaDenominator)
  · intro x _hx
    exact ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩
  · intro y _hy
    exact fabiusInv_mem_Icc F hF y
  · constructor
    · intro x hx
      exact fabiusInv_fabiusReal F hF hx
    · intro y hy
      exact fabiusReal_fabiusInv F hF hy
  · exact inverseFabiusDeltaDenominator_primrec.to_comp
  · intro p
    rw [inverseFabiusDeltaDenominator]
    positivity
  · intro p u v _hu _hv huv
    exact abs_fabiusInv_sub_lt_inverse_two_pow_of_lt_deltaDenominator
      F hF p huv

/-- The total inverse Fabius function is a computable real function: tolerant
bisection provides sequential computability, and the explicit logarithmic
Delta denominator provides effective uniform continuity. -/
theorem fabiusInv_isComputableRealFunction
    (F : BoundedFabius) (hF : IsFabius F) :
    IsComputableRealFunction (fabiusInv F hF) where
  sequentiallyComputable := by
    intro x hx
    have hclamp : ComputableRealSequence (fun i => unitClamp (x i)) :=
      unitClamp_sequentiallyComputable x hx
    have hout := fabiusInv_sequentiallyComputableOn_Icc F hF
      (fun i => unitClamp (x i)) hclamp (fun i => unitClamp_mem_Icc (x i))
    simpa only [fabiusInv_unitClamp] using hout
  effectivelyUniformContinuous :=
    fabiusInv_effectivelyUniformContinuous_logarithmicDelta F hF

end Fabius
