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

/-- Exponentiating the corrected logarithmic formula gives the asymptotic
equivalent requested in the linked Math Stack Exchange question. -/
theorem fabius_isEquivalent_exp_explicitCorrectedWikipediaMain
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => fabiusReal F x) ~[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => Real.exp (fabiusExplicitCorrectedWikipediaMain x)) := by
  have hscale : Tendsto (fun x : ℝ => (-Real.log x)⁻¹)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
  have herr : Tendsto
      (fun x : ℝ => Real.log (fabiusReal F x) -
        fabiusExplicitCorrectedWikipediaMain x)
      (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    (log_fabius_sub_explicitCorrectedWikipediaMain_isBigO F hF).trans_tendsto
      hscale
  have hexp : Tendsto
      (fun x : ℝ => Real.exp (Real.log (fabiusReal F x) -
        fabiusExplicitCorrectedWikipediaMain x))
      (nhdsWithin 0 (Ioi 0)) (nhds 1) := by
    convert Real.continuous_exp.continuousAt.tendsto.comp herr using 1
    · rfl
    · simp
  apply isEquivalent_of_tendsto_one
  apply hexp.congr'
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hFx : 0 < fabiusReal F x := fabius_pos_of_pos F hF hx
  rw [Real.exp_sub, Real.exp_log hFx]
  rfl

end Fabius
