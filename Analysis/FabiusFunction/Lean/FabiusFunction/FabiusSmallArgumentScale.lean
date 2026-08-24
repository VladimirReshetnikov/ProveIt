import FabiusFunction.FabiusLogScale
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-!
# Equivalence of logarithmic and small-argument scales

The maps `t ↦ 2⁻ᵗ` and `x ↦ -log₂ x` identify `t → ∞` with the
small-positive-argument filter `x → 0⁺`.  This module packages that exact
inverse relationship and transfers Big-O estimates between the two forms.
-/

set_option autoImplicit false

open Filter Asymptotics Set

namespace Fabius

/-- Inverse logarithmic coordinate to `fabiusLogArgument t = 2⁻ᵗ`. -/
noncomputable def fabiusSmallArgumentLog (x : ℝ) : ℝ :=
  -Real.logb 2 x

/-- The inverse logarithmic coordinate tends to infinity at zero from the right. -/
theorem fabiusSmallArgumentLog_tendsto_atTop :
    Tendsto fabiusSmallArgumentLog (nhdsWithin 0 (Ioi 0)) atTop := by
  exact tendsto_neg_atBot_atTop.comp
    (Real.tendsto_logb_nhdsGT_zero (by norm_num : (1 : ℝ) < 2))

/-- `2 ^ (-(-log₂ x)) = x` for positive `x`. -/
theorem fabiusLogArgument_smallArgumentLog {x : ℝ} (hx : 0 < x) :
    fabiusLogArgument (fabiusSmallArgumentLog x) = x := by
  unfold fabiusLogArgument fabiusSmallArgumentLog
  rw [neg_neg, Real.rpow_logb_eq_abs (by norm_num : (0 : ℝ) < 2)
    (by norm_num : (2 : ℝ) ≠ 1) hx.ne', abs_of_pos hx]

/-- `-log₂(2⁻ᵗ) = t`. -/
theorem fabiusSmallArgumentLog_logArgument (t : ℝ) :
    fabiusSmallArgumentLog (fabiusLogArgument t) = t := by
  unfold fabiusSmallArgumentLog fabiusLogArgument
  rw [Real.logb_rpow (by norm_num) (by norm_num)]
  ring

/-- Transfer a logarithmic-scale `O` estimate at `t → ∞` back to the
equivalent small-positive-argument filter. -/
theorem isBigO_smallArgument_of_logScale
    (f g : ℝ → ℝ)
    (h : (fun t => f (fabiusLogArgument t)) =O[atTop]
      (fun t => g (fabiusLogArgument t))) :
    f =O[nhdsWithin 0 (Ioi 0)] g := by
  have hc := h.comp_tendsto fabiusSmallArgumentLog_tendsto_atTop
  apply hc.congr'
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact congrArg f (fabiusLogArgument_smallArgumentLog hx)
  · filter_upwards [self_mem_nhdsWithin] with x hx
    exact congrArg g (fabiusLogArgument_smallArgumentLog hx)

end Fabius
