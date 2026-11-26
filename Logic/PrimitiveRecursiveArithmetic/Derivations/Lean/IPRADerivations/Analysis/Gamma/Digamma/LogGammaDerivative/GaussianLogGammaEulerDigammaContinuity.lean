import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Derivatives.GaussianLogGammaEulerSlopeContinuity
import IPRADerivations.Analysis.Gamma.Digamma.LogGammaDerivative.GaussianLogGammaEulerDigammaFractionsCofinal
import IPRADerivations.Analysis.Names.Rates.GaussianNamedLipschitzRate
import IPRADerivations.Analysis.Names.Rates.GaussianNamedRateTransport

/-!
# A fixed right-half-plane continuity modulus for the complex digamma

At a common cutoff the integer logarithm cancels. The uniform finite
reciprocal estimate and the original cofinal rates give a diagonal
envelope with constant `M²+2`. Rational slack removal gives the
same modulus at independent original observation clocks. The exact
C27 partial-fraction name inherits the bound by transport.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaContinuity

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerRepresentation (subst_argument)
open GaussianLogGammaEulerReciprocalSlope (reciprocalSum)
open GaussianLogGammaEulerResidualRadius (radius subst_radius)
open GaussianLogGammaEulerSlopeContinuity (input subst_input coefficient reciprocal_sum_lipschitz)
open GaussianNameEquivalence (cross_symm)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator rate_at denominator_positive)
open GaussianNamedLipschitzRate (diagonalEnvelope diagonalNumerator diagonalDenominator independent_rate)
open GaussianNamedRateTransport (transport)
open GaussianPositiveRationalLogarithm (logF)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded qsub subst_distanceBounded)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianRightHalfPlaneLogarithm (source)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "finiteF" => GaussianLogGammaEulerReciprocalSlope.nameF
local notation "finiteData" => GaussianLogGammaEulerReciprocalSlope.data
local notation "slopeF" => GaussianLogGammaEulerReciprocalSlopeCofinal.nameF
local notation "slopeData" => GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData
local notation "fractionsF" => GaussianLogGammaEulerDigammaFractionsCofinal.nameF
local notation "fractionsData" => GaussianLogGammaEulerDigammaFractionsCofinal.data
local notation "ld" => GaussianPositiveRationalLogarithm.data

private theorem readback (p A B D neg N : PTm n) (hN : Γ ⊢[PRAAx] le one N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 finiteF p (finiteData A B D neg N))
      (qsub (ap2 logF p (ld N one)) (reciprocalSum A B D neg (succ N))) (num 6) (unit p) := by
  let z := reciprocalSum A B D neg (succ N)
  let x := ld N one
  exact distance_congr (.eqRefl _) (qsub_congr (.eqRefl _) (constant_at p z)) (.eqRefl _) (.eqRefl _)
    (GaussianNamedDifference.sample_error logF constantF x z p
      (GaussianPositiveRationalLogarithm.name_regular N one (.andI hN (le_refl one))) (constant_regular z))

private theorem finite_at (p A B D neg a b d sign M H E N : PTm n)
    (h : Γ ⊢[PRAAx] input A D neg a d sign M) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N)
    (near : Γ ⊢[PRAAx] distanceBounded (argument A B D neg) (argument a b d sign) H E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 finiteF p (finiteData A B D neg N)) (ap2 finiteF p (finiteData a b d sign N))
      (coefficient M * H * unit p + num 12 * E) (E * unit p) := by
  let U := unit p
  let Q := E * U
  let v := coefficient M * H
  let l := ap2 logF p (ld N one)
  let r := reciprocalSum A B D neg (succ N)
  let s := reciprocalSum a b d sign (succ N)
  let x := ap2 finiteF p (finiteData A B D neg N)
  let y := ap2 finiteF p (finiteData a b d sign N)
  let a₀ := qsub l r
  let b₀ := qsub l s
  have hu := unit_positive (Γ := Γ) p
  have hq := positive_product _ _ hE hu
  have hr := reciprocal_sum_lipschitz A B D neg a b d sign M H E N h hE near
  have small := GaussianNamedDifference.difference_distance l l r s zero v E hE
    (GaussianRationalPowerDifference.distance_refl_zero l E hE) hr
  have middle : Γ ⊢[PRAAx] distanceBounded a₀ b₀ (v * U) Q :=
    distance_radius_mono a₀ b₀ _ _ _ _ hE hq
      (le_of_eq_add (d := zero) (by dsimp only [Q]; ipra_ring)) small
  have lift (c w : PTm n) (hc : Γ ⊢[PRAAx] distanceBounded c w (num 6) U) :
      Γ ⊢[PRAAx] distanceBounded c w (num 6 * E) Q :=
    distance_radius_mono c w _ _ _ _ hu hq (le_of_eq_add (d := zero) (by dsimp only [Q]; ipra_ring)) hc
  have left := lift x a₀ (readback p A B D neg N hN)
  have right := distance_symmetric y b₀ _ _ hq (lift y b₀ (readback p a b d sign N hN))
  have total := distance_triangle_same x b₀ y (num 6 * E + v * U) (num 6 * E) Q hq
    (distance_triangle_same x a₀ b₀ _ _ Q hq left middle) right
  exact distance_congr (.eqRefl x) (.eqRefl y) (by dsimp only [v, U]; ipra_ring) (.eqRefl Q) total

private theorem cofinal_side (p A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] distanceBounded (ap2 slopeF p (slopeData A B D neg)) (ap2 finiteF p (finiteData A B D neg (unit p)))
      (radius A B + num 3) (unit p) := by
  let N := unit p
  let R := radius A B
  have hN := unit_positive (Γ := Γ) p
  have actual := GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_cutoff_rate A B D neg N h hN
  have comparison := rate_at slopeF finiteF (slopeData A B D neg) (finiteData A B D neg N) (R + one) N p p actual
  exact distance_radius_mono _ _ _ _ _ _ (denominator_positive N p p hN) hN
    (le_of_eq_add (d := zero) (by dsimp only [N, R, rateNumerator, rateDenominator]; ipra_ring)) comparison

private def samplingCost (A B a b : PTm n) : PTm n := radius A B + radius a b + num 18

private theorem diagonal_gap (p A B D neg a b d sign M H E : PTm n)
    (h : Γ ⊢[PRAAx] input A D neg a d sign M) (hE : Γ ⊢[PRAAx] le one E)
    (near : Γ ⊢[PRAAx] distanceBounded (argument A B D neg) (argument a b d sign) H E) :
    Γ ⊢[PRAAx] distanceBounded (ap2 slopeF p (slopeData A B D neg)) (ap2 slopeF p (slopeData a b d sign))
      (diagonalNumerator (coefficient M * H) E (samplingCost A B a b) p) (diagonalDenominator E p) := by
  let U := unit p
  let Q := E * U
  let x := ap2 slopeF p (slopeData A B D neg)
  let y := ap2 slopeF p (slopeData a b d sign)
  let a₀ := ap2 finiteF p (finiteData A B D neg U)
  let b₀ := ap2 finiteF p (finiteData a b d sign U)
  let V := coefficient M * H * U + num 12 * E
  let L := (radius A B + num 3) * E
  let R := (radius a b + num 3) * E
  have hu := unit_positive (Γ := Γ) p
  have hq := positive_product _ _ hE hu
  have lift (c w T : PTm n) (hc : Γ ⊢[PRAAx] distanceBounded c w T U) :
      Γ ⊢[PRAAx] distanceBounded c w (T * E) Q :=
    distance_radius_mono c w _ _ _ _ hu hq (le_of_eq_add (d := zero) (by dsimp only [Q]; ipra_ring)) hc
  have left := lift x a₀ _ (cofinal_side p A B D neg h.andE₁)
  have middle := finite_at p A B D neg a b d sign M H E U h hE hu near
  have right := distance_symmetric y b₀ _ _ hq (lift y b₀ _ (cofinal_side p a b d sign h.andE₂.andE₁))
  have total := distance_triangle_same x b₀ y (L + V) R Q hq
    (distance_triangle_same x a₀ b₀ L V Q hq left middle) right
  exact distance_congr (.eqRefl x) (.eqRefl y)
    (by dsimp only [L, V, R, diagonalNumerator, samplingCost]; ipra_ring) (.eqRefl Q) total

/-- An independent observation modulus for the original cofinal reciprocal slope. -/
theorem canonical_slope_lipschitz (A B D neg a b d sign M H E : PTm n)
    (h : Γ ⊢[PRAAx] input A D neg a d sign M) (hE : Γ ⊢[PRAAx] le one E)
    (near : Γ ⊢[PRAAx] distanceBounded (argument A B D neg) (argument a b d sign) H E) :
    Γ ⊢[PRAAx] independentRate slopeF slopeF (slopeData A B D neg) (slopeData a b d sign) (coefficient M * H) E := by
  apply independent_rate slopeF slopeF _ _ (coefficient M * H) E (samplingCost A B a b) hE
    (GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_regular A B D neg h.andE₁)
    (GaussianLogGammaEulerReciprocalSlopeCofinal.canonical_regular a b d sign h.andE₂.andE₁)
  refine .allI ?_
  let s (v : PTm n) := Syn.shift v
  let Δ := Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] input (s A) (s D) (s neg) (s a) (s d) (s sign) (s M) := by
    simpa only [Δ, s, Fm.shift, Syn.shift, subst_input] using h.shift
  have he : Δ ⊢[PRAAx] le one (s E) := by simpa [Δ, s, Fm.shift, Syn.shift] using hE.shift
  have hd : Δ ⊢[PRAAx] distanceBounded (argument (s A) (s B) (s D) (s neg))
      (argument (s a) (s b) (s d) (s sign)) (s H) (s E) := by
    simpa only [Δ, s, Fm.shift, Syn.shift, subst_distanceBounded, subst_argument] using near.shift
  simpa only [Δ, s, Syn.shift, diagonalEnvelope, GaussianLogGammaEulerReciprocalSlopeCofinal.canonicalData,
    GaussianLogGammaEulerReciprocalSlopeCofinal.subst_data, subst_radius, PTm.subst_add, PTm.subst_mul,
    PTm.subst_num, coefficient, samplingCost, two, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using
    diagonal_gap (var 0) (s A) (s B) (s D) (s neg) (s a) (s b) (s d) (s sign) (s M) (s H) (s E) hs he hd

/-- The C27 partial-fraction name has the same uniform two-input modulus. -/
theorem canonical_fraction_lipschitz (A B D neg a b d sign M H E : PTm n)
    (h : Γ ⊢[PRAAx] input A D neg a d sign M) (hE : Γ ⊢[PRAAx] le one E)
    (near : Γ ⊢[PRAAx] distanceBounded (argument A B D neg) (argument a b d sign) H E) :
    Γ ⊢[PRAAx] independentRate fractionsF fractionsF (fractionsData A B D neg) (fractionsData a b d sign) (coefficient M * H) E :=
  transport slopeF slopeF fractionsF fractionsF _ _ _ _ (coefficient M * H) E hE
    (canonical_slope_lipschitz A B D neg a b d sign M H E h hE near)
    (cross_symm _ _ _ _ (GaussianLogGammaEulerDigammaFractionsCofinal.cofinal_equivalent A B D neg h.andE₁))
    (cross_symm _ _ _ _ (GaussianLogGammaEulerDigammaFractionsCofinal.cofinal_equivalent a b d sign h.andE₂.andE₁))

theorem actual_canonical_complex_digamma_Lipschitz_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
      (input (var 0) (var 2) (var 3) (var 4) (var 6) (var 7) (var 8) ⟶ le one (var 10) ⟶
        distanceBounded (argument (var 0) (var 1) (var 2) (var 3)) (argument (var 4) (var 5) (var 6) (var 7))
          (var 9) (var 10) ⟶
        independentRate fractionsF fractionsF (fractionsData (var 0) (var 1) (var 2) (var 3))
          (fractionsData (var 4) (var 5) (var 6) (var 7)) (coefficient (var 8) * var 9) (var 10)) :=
  closeUniv 11 (.impI (.impI (.impI (canonical_fraction_lipschitz _ _ _ _ _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerDigammaContinuity
