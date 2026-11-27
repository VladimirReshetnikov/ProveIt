import IPRADerivations.Analysis.Gamma.Digamma.LogGammaDerivative.Fractions.GaussianLogGammaEulerDigammaFractions
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.ReciprocalSlopes.GaussianLogGammaEulerReciprocalSlopeCofinal
import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaEulerDerivative
import IPRADerivations.Analysis.Beta.Endpoints.Upper.GaussianBetaUpperPowerCancellation

/-!
# The cofinal complex Euler slope has the actual digamma partial fractions

At any positive cutoff the difference from the original finite slope is
controlled by the Euler–Mascheroni error in `H_N − log N`. The checked
cofinal slope therefore lies within `(R+2)/N` of the literal regular
partial-fraction names, with the original errors at independent clocks.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaFractionsRate

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular harmonicPoint)
open GaussianGammaDerivativeAtOne (negativeGammaF negativeGammaData negativeGamma_regular)
open GaussianLogGammaEulerDigammaFractions (correction correction_value)
open GaussianLogGammaEulerReciprocalSlope (reciprocalSum)
open GaussianLogGammaEulerResidualRadius (radius subst_radius)
open GaussianNameEquivalence (cross_at)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator independent_rate)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (qadd positive_product)
open GaussianRationalMetric (qsub qnegative distanceBounded)
open GaussianRationalSyntheticDivision (qadd_congr qsub_congr)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "cofinalF" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "cofinalData" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
local notation "slopeF" => GaussianLogGammaEulerReciprocalSlope.nameF
local notation "slopeData" => GaussianLogGammaEulerReciprocalSlope.data
local notation "fractionsF" => GaussianLogGammaEulerDigammaFractions.nameF
local notation "fractionsData" => GaussianLogGammaEulerDigammaFractions.data
local notation "originalLogF" => GaussianPositiveRationalLogarithm.logF
local notation "logData" => GaussianPositiveRationalLogarithm.data
local notation "integerLogF" => GaussianGammaFiniteApproximantName.logF

private theorem log_harmonic_error (p N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 originalLogF p (logData N one))
      (qadd (ap2 negativeGammaF p negativeGammaData) (harmonicPoint N))
      (unit p + num 10 * N) (N * unit p) := by
  let U := unit p
  let Q := N * U
  let x := ap2 originalLogF p (logData N one)
  let y := ap2 integerLogF p N
  let z := qadd (ap2 negativeGammaF p negativeGammaData) (harmonicPoint N)
  have hu := unit_positive (Γ := Γ) p
  have hq := positive_product _ _ hN hu
  have logCross := GaussianBetaUpperPowerCancellation.rational_log_integer N hN
  have round : Γ ⊢[PRAAx] distanceBounded x y (two * N) Q :=
    distance_radius_mono x y (U + U) (U * U) _ _ (positive_product _ _ hu hu) hq
      (le_of_eq_add (d := zero) (by dsimp only [Q]; ipra_ring))
      (cross_at originalLogF integerLogF (logData N one) N p p logCross)
  have error := GaussianGammaDigammaEulerDerivative.log_sample_error p N hN
  exact distance_congr (.eqRefl x) (.eqRefl z) (by ipra_ring) (.eqRefl Q)
    (distance_triangle_same x y z (two * N) (U + num 8 * N) Q hq round error)

/-- The finite discrepancy is exactly the original log-harmonic error up to sampling. -/
theorem finite_gap (p A B D neg N : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 slopeF p (slopeData A B D neg N)) (ap2 fractionsF p (fractionsData A B D neg N))
      (unit p + num 19 * N) (N * unit p) := by
  let U := unit p
  let Q := N * U
  let s := reciprocalSum A B D neg (succ N)
  let c := correction A B D neg N
  let g := ap2 negativeGammaF p negativeGammaData
  let h := harmonicPoint N
  let l := ap2 originalLogF p (logData N one)
  let rawSlope := qsub l s
  let rawFractions := qsub (qadd g h) s
  let x := ap2 slopeF p (slopeData A B D neg N)
  let y := ap2 fractionsF p (fractionsData A B D neg N)
  have hu := unit_positive (Γ := Γ) p
  have hq := positive_product _ _ hN hu
  have lift (a b E : PTm n) (close : Γ ⊢[PRAAx] distanceBounded a b E U) :
      Γ ⊢[PRAAx] distanceBounded a b (E * N) Q :=
    distance_radius_mono a b E U _ _ hu hq (le_of_eq_add (d := zero) (by dsimp only [Q]; ipra_ring)) close
  have slopeSample := GaussianNamedDifference.sample_error originalLogF constantF (logData N one) s p
    (GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))) (constant_regular s)
  have readSlope : Γ ⊢[PRAAx] distanceBounded x rawSlope (num 6 * N) Q :=
    lift x rawSlope (num 6) (distance_congr (.eqRefl x) (qsub_congr (.eqRefl l) (constant_at p s))
      (.eqRefl _) (.eqRefl _) slopeSample)
  have rawGap : Γ ⊢[PRAAx] distanceBounded rawSlope rawFractions (U + num 10 * N) Q :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (GaussianNamedDifference.difference_distance l (qadd g h) s s (U + num 10 * N) zero Q hq
        (log_harmonic_error p N hN) (GaussianRationalPowerDifference.distance_refl_zero s Q hq))
  have fractionSample := GaussianNameRingLaws.add_sample_error (Γ := Γ) negativeGammaF constantF negativeGammaData c p
    negativeGamma_regular (constant_regular c)
  have regroup : Γ ⊢[PRAAx] qadd g (ap2 constantF p c) ≐ rawFractions :=
    (qadd_congr (.eqRefl g) ((constant_at p c).eqTrans (correction_value A B D neg N hD))).eqTrans
      (GaussianRationalSumAlgebra.qadd_associative g h (qnegative s)).eqSymm
  have readFractions : Γ ⊢[PRAAx] distanceBounded y rawFractions (GaussianNameRingLaws.three * N) Q :=
    lift y rawFractions GaussianNameRingLaws.three
      (distance_congr (.eqRefl y) regroup (.eqRefl _) (.eqRefl _) fractionSample)
  have total := distance_triangle_same x rawFractions y (num 6 * N + (U + num 10 * N))
    (GaussianNameRingLaws.three * N) Q hq
    (distance_triangle_same x rawSlope rawFractions _ _ Q hq readSlope rawGap)
    (distance_symmetric y rawFractions _ _ hq readFractions)
  exact distance_congr (.eqRefl x) (.eqRefl y) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl Q) total

private theorem diagonal_gap (p A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 cofinalF p (cofinalData A B D neg)) (ap2 fractionsF p (fractionsData A B D neg N))
      (diagonalNumerator (radius A B + two) N (num 21) p) (diagonalDenominator N p) := by
  let U := unit p
  let Q := N * U
  let R := radius A B
  let x := ap2 cofinalF p (cofinalData A B D neg)
  let y := ap2 slopeF p (slopeData A B D neg N)
  let z := ap2 fractionsF p (fractionsData A B D neg N)
  let B₀ := (R + one) * U + two * N
  have hq := positive_product _ _ hN (unit_positive p)
  have rate := GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_cutoff_rate A B D neg N h hN
  have raw := rate_at cofinalF slopeF (cofinalData A B D neg) (slopeData A B D neg N) (R + one) N p p rate
  have middle : Γ ⊢[PRAAx] distanceBounded x y B₀ Q :=
    distance_radius_mono x y _ _ B₀ Q (denominator_positive N p p hN) hq
      (le_of_eq_add (d := zero) (by dsimp only [B₀, Q, rateNumerator, rateDenominator]; ipra_ring)) raw
  exact distance_congr (.eqRefl x) (.eqRefl z) (by dsimp only [B₀, R, diagonalNumerator]; ipra_ring) (.eqRefl Q)
    (distance_triangle_same x y z B₀ (U + num 19 * N) Q hq middle (finite_gap p A B D neg N h.andE₂ hN))

/-- The original cofinal complex slope is the limit of the literal partial-fraction names. -/
theorem canonical_fraction_rate (A B D neg N : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] independentRate cofinalF fractionsF (cofinalData A B D neg) (fractionsData A B D neg N)
      (radius A B + two) N := by
  apply independent_rate cofinalF fractionsF _ _ (radius A B + two) N (num 21) hN
    (GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_regular A B D neg h)
    (GaussianLogGammaEulerDigammaFractions.name_regular A B D neg N)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  have hs : Γ.map Fm.shift ⊢[PRAAx] source (s A) (s D) (s neg) := by
    simpa [s, Fm.shift, Syn.shift, source, GaussianRightHalfPlaneArgument.source] using h.shift
  have hn : Γ.map Fm.shift ⊢[PRAAx] le one (s N) := by simpa [s, Fm.shift, Syn.shift] using hN.shift
  simpa only [diagonalEnvelope, Syn.shift, s, GaussianLogGammaEulerDigammaFractions.subst_data,
    GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData, GaussianLogGammaEulerReciprocalSlopeCofinal.subst_data,
    subst_radius, PTm.subst_add, two, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, PTm.subst_num] using
    diagonal_gap (var 0) (s A) (s B) (s D) (s neg) (s N) hs hn

theorem actual_complex_digamma_partial_fraction_rate_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 2) (var 3) ⟶ le one (var 4) ⟶
        independentRate cofinalF fractionsF (cofinalData (var 0) (var 1) (var 2) (var 3))
          (fractionsData (var 0) (var 1) (var 2) (var 3) (var 4)) (radius (var 0) (var 1) + two) (var 4)) :=
  closeUniv 5 (.impI (.impI (canonical_fraction_rate _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaFractionsRate
