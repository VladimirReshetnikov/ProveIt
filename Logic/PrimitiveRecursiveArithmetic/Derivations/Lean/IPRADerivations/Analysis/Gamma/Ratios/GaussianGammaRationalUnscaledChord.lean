import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalFractionalChord
import IPRADerivations.Analysis.Names.Scaling.GaussianNamedNaturalScaleOrder
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicWeightedQuadraticName
import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingNames

/-!
# Fractional-power logarithms and unscaled strict Gamma chords

The positive natural scale of the exact rational chord is reflected
on the actual names. Its time coefficient becomes the original
positive rational fraction used to define a real power.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalUnscaledChord

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaRationalFractionalChord (gammaF gammaData harmonicF harmonicData harmonic_regular)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (ofGaussian_canonical qmul)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "C" => constantF
local notation "L" => harmonicF
local notation "P" => logGammaF

def fractionalData (r b a D : PTm n) : PTm n := multiplyData C H (fraction r b) (hd a D)

theorem fractional_regular (r b a D : PTm n) (hs : Γ ⊢[PRAAx] source a D) :
    Γ ⊢[PRAAx] pointCN L (fractionalData r b a D) :=
  multiply_fast _ _ _ _ (constant_regular _) (GaussianHarmonicLogarithmName.name_regular a D hs)

theorem fractional_real (r b a D : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realSamples L (fractionalData r b a D) :=
  GaussianStirlingNames.multiply_real _ _ _ _
    (GaussianStirlingNames.constant_real (fraction r b) (ofGaussian_canonical _ _ hb)
      (GaussianStirlingNames.fraction_axis r b hb))
    (GaussianStirlingNames.log_x_real a D)

theorem fraction_cancels (r b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qmul (naturalPoint b) (fraction r b) ≐ naturalPoint r := by
  have e := GaussianEulerDampedTimeRate.fraction_product b one r b (le_refl one) hb
  have f := GaussianGammaEulerMidpointLogHeadGap.fraction_congr (Γ := Γ) (.eqRefl (b*r)) (mul_comm one b)
  exact e.eqTrans (f.eqTrans (GaussianCompactRiemannSplit.fraction_cancel b r one hb (le_refl one)))

theorem scaled_fractional (r b a D : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hs : Γ ⊢[PRAAx] source a D) :
    Γ ⊢[PRAAx] crossEquivalent (productF L) L (productData L b (fractionalData r b a D)) (harmonicData r a D) := by
  let X := naturalPoint b
  let R := fraction r b
  let W := naturalPoint r
  let Y := hd a D
  have hx := constant_regular (Γ := Γ) X
  have hr := constant_regular (Γ := Γ) R
  have hw := constant_regular (Γ := Γ) W
  have hy := GaussianHarmonicLogarithmName.name_regular a D hs
  have decompose := GaussianNameRingLaws.multiply_associative C C H X R Y hx hr hy
  have point := cross_trans _ _ _ _ _ _ (GaussianGammaWeierstrassApproximant.constant_product_cross X R)
    (GaussianGammaWeierstrassApproximant.constant_data_cross _ _ (fraction_cancels r b hb))
  have reduce := GaussianGammaAdjacentCutoff.multiply_cross (multiplyF C C) C H H
    (multiplyData C C X R) W Y Y (multiply_fast _ _ _ _ hx hr) hw hy hy point (cross_refl _ _ hy)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ decompose) reduce

theorem scaled_rhs (b r a D c d : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (ha : Γ ⊢[PRAAx] source a D) (hc : Γ ⊢[PRAAx] source c d) :
    Γ ⊢[PRAAx] crossEquivalent (productF (addF L P)) (addF L gammaF)
      (productData (addF L P) b (addData (fractionalData r b a D) (logGammaData c d)))
      (addData (harmonicData r a D) (gammaData b c d)) := by
  let X := fractionalData r b a D
  let Y := logGammaData c d
  let U := productData L b X
  let V := gammaData b c d
  have hx := fractional_regular r b a D ha
  have hy := log_gamma_regular c d hc
  have hU := GaussianNamedNaturalScaleOrder.regular L b X hx
  have hV := GaussianNamedNaturalScaleOrder.regular P b Y hy
  have split := GaussianNameRingLaws.distributive C L P (naturalPoint b) X Y (constant_regular _) hx hy
  have b' := GaussianNamedGammaHalfShift.add_cross (productF L) L gammaF gammaF U (harmonicData r a D) V V
    hU (harmonic_regular r a D ha) hV hV (scaled_fractional r b a D hb ha) (cross_refl _ _ hV)
  exact cross_trans _ _ _ _ _ _ split b'

theorem chord (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] strictOrder P (addF L P)
      (logGammaData (a+r) b) (addData (fractionalData r b a b) (logGammaData a b)) := by
  have hA : Γ ⊢[PRAAx] source a b := .andI ha hb
  have hY : Γ ⊢[PRAAx] source (a+r) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hx := log_gamma_regular (a+r) b hY
  have hy := add_fast _ _ _ _ (fractional_regular r b a b hA) (log_gamma_regular a b hA)
  apply GaussianNamedNaturalScaleOrder.reflect_strict _ _ b _ _ hb hx hy
  exact strict_transport _ _ _ _ _ _ _ _ (cross_refl _ _ (GaussianNamedNaturalScaleOrder.regular _ _ _ hx))
    (cross_symm _ _ _ _ (scaled_rhs b r a b a b hb hA hA))
    (GaussianGammaRationalFractionalChord.chord a b r s ha hb hr hs he)

theorem complementary_chord (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] strictOrder P (addF L P) (logGammaData (a+b) b)
      (addData (fractionalData s b (a+r) b) (logGammaData (a+r) b)) := by
  have hY : Γ ⊢[PRAAx] source (a+r) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hZ : Γ ⊢[PRAAx] source (a+b) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hx := log_gamma_regular (a+b) b hZ
  have hy := add_fast _ _ _ _ (fractional_regular s b (a+r) b hY) (log_gamma_regular (a+r) b hY)
  apply GaussianNamedNaturalScaleOrder.reflect_strict _ _ b _ _ hb hx hy
  exact strict_transport _ _ _ _ _ _ _ _ (cross_refl _ _ (GaussianNamedNaturalScaleOrder.regular _ _ _ hx))
    (cross_symm _ _ _ _ (scaled_rhs b s (a+r) b (a+r) b hb hY hY))
    (GaussianGammaRationalFractionalChord.complementary_chord a b r s ha hb hr hs he)

end LeanProofs.IPRA.Analysis.GaussianGammaRationalUnscaledChord
