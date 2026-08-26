import FabiusFunction.FabiusLambertPhase
import FabiusFunction.FabiusSharpLambertTransfer
import FabiusFunction.FabiusSmallArgumentScale
import FabiusFunction.SaddleExpansionAlgebra

/-!
# The forward Laplace tail is flat on the Lambert scale

The sharp-transfer module proves that exponential decay in the saddle radius
makes the forward dyadic-Laplace tail smaller than every inverse power of the
lower-Lambert phase.  This module transfers that estimate to small positive
arguments and packages the tail as a flat asymptotic expansion.
-/

set_option autoImplicit false

open Filter Asymptotics

namespace Fabius

/-- Small-positive-argument form of the arbitrary-order tail estimate. -/
theorem negativeLaplaceTailError_lambert_isBigO_inv_pow
    (N : ℕ) :
    (fun x : ℝ => negativeLaplaceTailError (fabiusLambertRadius x))
      =O[nhdsWithin 0 (Set.Ioi 0)]
        (fun x : ℝ => (fabiusLambertPhase x)⁻¹ ^ N) := by
  apply isBigO_smallArgument_of_logScale
  simpa only [fabiusLogArgument, fabiusLambertRadius_dyadic,
    fabiusLambertPhase_dyadic] using
      negativeLaplaceTailError_dyadicLambert_isBigO_inv_pow N

/-- In the generic Poincare-expansion API the forward product tail has the
identically-zero coefficient sequence: it is flat to all orders. -/
theorem negativeLaplaceTailError_dyadicLambert_hasAsymptoticExpansion :
    SaddleExpansion.HasAsymptoticExpansion atTop
      (fun t : ℝ => (fabiusLambertPhase ((2 : ℝ) ^ (-t)))⁻¹)
      (fun t : ℝ => negativeLaplaceTailError
        (fabiusLambertRadius ((2 : ℝ) ^ (-t))))
      (fun _ _ => (0 : ℝ)) := by
  constructor
  · intro _k
    apply IsBigO.of_bound 0
    filter_upwards with _t
    norm_num
  · intro N
    simpa [SaddleExpansion.partialSum] using
      negativeLaplaceTailError_dyadicLambert_isBigO_inv_pow N

end Fabius
