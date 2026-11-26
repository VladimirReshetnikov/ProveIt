import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.GaussianGammaDigammaTwoShiftRate
import IPRADerivations.Analysis.Gamma.Digamma.TwoShift.Rational.GaussianGammaDigammaTwoShiftExponentialCaps
import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingMultiplicativeBoundsOrder

/-!
# Relative error of the original two-shift Gamma quotient

If x≥max(2A+1, 4A(A+1)), the original normalized quotient lies in
the exact interval [1−8A(A+1)/x, 1+8A(A+1)/x].
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRelativeRate

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaDigammaTwoShiftBinding
  (powerLogF powerLogData denominatorLogF denominatorLogData quotientLogF quotientLogData quotientF quotientData quotient_log_regular)
open GaussianGammaDigammaTwoShiftExponentialCaps (lower upperPoint constant_caps)
open GaussianGammaDigammaTwoShiftWindow (input coefficient positive_endpoint)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (ofGaussian_canonical)
open GaussianRationalMetric (qnegative qsub_canonical qnegative_canonical)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData)
open GaussianStirlingNames (constant_real multiply_real add_real fraction_axis log_gamma_real log_x_real)
open RationalGaussianEmbedding (axis_add axis_negative)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => exponentialInputData

theorem quotient_log_real (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realSamples quotientLogF (quotientLogData a b c d) := by
  let w := GaussianGammaDigammaTwoShiftBinding.coefficient b c d
  let l := powerLogData a b c d
  let y := denominatorLogData a b c d
  have hc := axis_add (fraction c b) (qnegative (fraction d b)) (fraction_axis c b hb)
    (axis_negative _ (fraction_axis d b hb))
  have hW := constant_real w (qsub_canonical _ _) hc
  have hL := multiply_real constantF H w (hd a b) hW (log_x_real a b)
  have hY := add_real logGammaF powerLogF (logGammaData d b) l (log_gamma_real d b) hL
  exact add_real logGammaF (negativeF denominatorLogF) (logGammaData c b) (negativeData y)
    (log_gamma_real c b) (GaussianNamedDampingPowerRealSamples.negative_real _ _ hY)

def relativeRate (a b c d A : PTm n) : Fm PTm n :=
  realOrder constantF quotientF (lower (coefficient b A) a) (quotientData a b c d) ⋏
  realOrder quotientF constantF (quotientData a b c d) (upperPoint (coefficient b A) a)

theorem two_shift_relative_rate (a b c d A : PTm n) (hs : Γ ⊢[PRAAx] input a b c d A)
    (hSize : Γ ⊢[PRAAx] le (coefficient b A) a) : Γ ⊢[PRAAx] relativeRate a b c d A := by
  let K := coefficient b A
  let q := fraction K a
  let v := qnegative q
  let x := quotientLogData a b c d
  have ha := hs.andE₁
  have hB := hs.andE₁.andE₂
  have hA := hs.andE₁.andE₁
  have base := hs.andE₂.andE₂.andE₁
  have hc := positive_endpoint a b A c hB base hs.andE₂.andE₂.andE₂.andE₁
  have hD := positive_endpoint a b A d hB base hs.andE₂.andE₂.andE₂.andE₂
  have hq := constant_real q (ofGaussian_canonical _ _ hA) (fraction_axis K a hA)
  have hv := constant_real v (qnegative_canonical _) (axis_negative _ (fraction_axis K a hA))
  have hx := quotient_log_regular a b c d ha hc hD
  have hr := quotient_log_real a b c d hB
  have localLog := GaussianGammaDigammaTwoShiftRate.two_shift_log_rate a b c d A hs
  have lo := GaussianStirlingMultiplicativeBoundsOrder.exponential_order constantF quotientLogF v x
    (constant_regular _) hx hv hr localLog.andE₁
  have hi := GaussianStirlingMultiplicativeBoundsOrder.exponential_order quotientLogF constantF x q
    hx (constant_regular _) hr hq localLog.andE₂
  have caps := constant_caps K a hA hSize
  exact .andI
    (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ caps.andE₁ lo)
    (GaussianEulerPowerChartTimeOrder.order_trans _ _ _ _ _ _ hi caps.andE₂)

theorem actual_original_Gamma_two_shift_relative_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (input (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        le (coefficient (var 1) (var 4)) (var 0) ⟶
        relativeRate (var 0) (var 1) (var 2) (var 3) (var 4)) :=
  closeUniv 5 (.impI (.impI (two_shift_relative_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaTwoShiftRelativeRate
