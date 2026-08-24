import FabiusFunction.FabiusSaddleCentralLambert
import FabiusFunction.FabiusExplicitSharpTransfer
import FabiusFunction.FabiusWikipediaObstruction
import FabiusFunction.FabiusDyadicSharpAsymptotic
import FabiusFunction.PeriodicFourier
import FabiusFunction.FabiusQuotientExponentialMismatch

/-!
# Sharp small-argument asymptotics of the Fabius function

This module closes the quantitative saddle argument and exposes its
source-facing consequences.  The elementary expression printed in the linked
Math Stack Exchange discussion is missing a genuine nonconstant periodic
term.  Adding `negativeLaplacePsi` at the exact lower-Lambert phase gives an
`O(1 / (-log x))` error; deleting it does not.

The related quotient-of-exponentials approximation is imported here as well.
It is a useful numerical fit on a compact interval, but its endpoint decay is
strictly faster than the Fabius bump and hence it is not an asymptotic
equivalent.
-/

set_option autoImplicit false

open Filter Set Asymptotics

namespace Fabius

/-- Unconditional compact Lambert-coordinate form of the corrected sharp
small-argument asymptotic. -/
theorem log_fabius_sub_correctedWikipediaMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusCorrectedWikipediaMain x) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => (-Real.log x)⁻¹) :=
  log_fabius_sub_correctedWikipediaMain_isBigO_of_kernelMass F hF
    (SaddleLambert.fabiusSaddleKernelMass_dyadicLambert_sub_one_isBigO F hF)

/-- Unconditional literal `log x`/`log (-log x)` expansion, corrected by the
nonconstant periodic term at the exact lower-Lambert phase. -/
theorem log_fabius_sub_explicitCorrectedWikipediaMain_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusExplicitCorrectedWikipediaMain x) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => (-Real.log x)⁻¹) :=
  log_fabius_sub_explicitCorrectedWikipediaMain_isBigO_of_kernelMass F hF
    (SaddleLambert.fabiusSaddleKernelMass_dyadicLambert_sub_one_isBigO F hF)

/-- The same `O(1 / (-log x))` claim is false for the uncorrected elementary
formula because its omitted periodic correction is nonzero. -/
theorem log_fabius_sub_WikipediaElementaryMain_not_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    ¬ ((fun x : ℝ => Real.log (fabiusReal F x) -
          fabiusWikipediaElementaryMain x) =O[nhdsWithin 0 (Ioi 0)]
        (fun x : ℝ => (-Real.log x)⁻¹)) :=
  log_fabius_sub_WikipediaElementaryMain_not_isBigO_of_kernelMass F hF
    (SaddleLambert.fabiusSaddleKernelMass_dyadicLambert_sub_one_isBigO F hF)

end Fabius
