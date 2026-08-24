import FabiusFunction.FabiusSharpLambertTransfer
import FabiusFunction.FabiusWikipediaMain
import FabiusFunction.FabiusLambertRates

/-!
# Final transfer to the corrected small-argument formula

This module packages the last source-facing reduction.  Once the normalized
Lambert-saddle kernel is `1 + O(1/λ)`, the exact saddle algebra, periodic
phase, and logarithmic coordinate equivalence give the corrected Wikipedia
formula with its literal `O(1/(-log x))` error at `x → 0⁺`.
-/

set_option autoImplicit false

open Filter Asymptotics Set

namespace Fabius

/-- The quantitative normalized-kernel estimate implies the corrected
Wikipedia asymptotic at small positive arguments. -/
theorem log_fabius_sub_correctedWikipediaMain_isBigO_of_kernelMass
    (F : BoundedFabius) (hF : IsFabius F)
    (hkernel :
      (fun t : ℝ => fabiusSaddleKernelMass F ((2 : ℝ) ^ (-t))
          (fabiusLambertRadius ((2 : ℝ) ^ (-t)))
          (fabiusLambertPhase ((2 : ℝ) ^ (-t))) - 1) =O[atTop]
        (fun t : ℝ => (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹)) :
    (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusCorrectedWikipediaMain x) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => (-Real.log x)⁻¹) := by
  have hmain :=
    log_fabius_dyadicReal_sub_sharpLambertMain_isBigO_of_kernelMass F hF hkernel
  have hcorrected :
      (fun t : ℝ => Real.log (fabiusReal F (fabiusLogArgument t)) -
          fabiusCorrectedWikipediaMain (fabiusLogArgument t)) =O[atTop]
        (fun t : ℝ => (dyadicLambertPhase t)⁻¹) := by
    apply hmain.congr'
    · filter_upwards [eventually_dyadicLambertPhase_domain] with t hsmall
      change Real.log (fabiusReal F ((2 : ℝ) ^ (-t))) -
          fabiusSharpLambertMain ((2 : ℝ) ^ (-t)) =
        Real.log (fabiusReal F ((2 : ℝ) ^ (-t))) -
          fabiusCorrectedWikipediaMain ((2 : ℝ) ^ (-t))
      rw [fabiusCorrectedWikipediaMain_eq_sharpLambertMain
        (Real.rpow_pos_of_pos (by norm_num) _) hsmall]
    · filter_upwards with t
      rw [fabiusLambertPhase_dyadic]
  exact isBigO_smallArgument_log_of_lambertScale
    (fun x : ℝ => Real.log (fabiusReal F x) -
      fabiusCorrectedWikipediaMain x) hcorrected

end Fabius
