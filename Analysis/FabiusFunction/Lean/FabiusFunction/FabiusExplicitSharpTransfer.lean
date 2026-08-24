import FabiusFunction.FabiusSharpAsymptoticTransfer
import FabiusFunction.FabiusWikipediaExpansion

/-!
# Transfer to the literal corrected Wikipedia expression

This is the source-facing end of the saddle reduction.  It combines the
compact lower-Lambert transfer with the exact expansion into logarithms and
Euler--Stieltjes constants.  The sole remaining hypothesis is the normalized
kernel-mass estimate; all phase and formula-conversion errors are discharged
here.
-/

set_option autoImplicit false

open Filter Asymptotics Set

namespace Fabius

/-- A normalized `O(1/λ)` saddle-kernel estimate implies the literal
corrected Wikipedia formula with error `O(1/(-log x))` at `x → 0⁺`. -/
theorem log_fabius_sub_explicitCorrectedWikipediaMain_isBigO_of_kernelMass
    (F : BoundedFabius) (hF : IsFabius F)
    (hkernel :
      (fun t : ℝ => fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
          (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
          (fabiusLambertPhase ((2 : ℝ) ^ (-t))) - 1) =O[atTop]
        (fun t : ℝ => (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹)) :
    (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusExplicitCorrectedWikipediaMain x) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => (-Real.log x)⁻¹) := by
  have hcompact :=
    log_fabius_sub_correctedWikipediaMain_isBigO_of_kernelMass F hF hkernel
  have hexpansion := fabiusCorrectedWikipediaMain_sub_explicit_isBigO
  have hsum := hcompact.add hexpansion
  apply hsum.congr' ?_ Filter.EventuallyEq.rfl
  filter_upwards with x
  ring

end Fabius
