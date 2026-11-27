import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalUnscaledChord
import IPRADerivations.Analysis.Names.Differences.GaussianNamedStrictOrderDifference
import IPRADerivations.Analysis.Stirling.Expansions.OddSeries.GaussianStirlingOddCoefficients
import IPRADerivations.Analysis.Logarithm.PositiveAxis.Bounds.GaussianPositiveRationalLogarithmOrder

/-!
# The exact rational Gautschi comparison in logarithms

The two fractional chords give the lower and upper logarithmic
estimates for `Γ(x+1)/Γ(x+u)`. The coefficients sum to one on
the literal fractional-power logarithm names.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalLogGautschi

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaRationalFractionalChord (harmonicF harmonicData)
open GaussianGammaRationalUnscaledChord (fractionalData fractional_regular fractional_real scaled_fractional)
open GaussianNameArithmetic (addF addData add_fast multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (add_associative multiply_one_left oneF one_fast)
open GaussianNamedGammaHalfShift (add_cross constant_sum)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalNaturalScale (naturalPoint)
open GaussianRationalSyntheticDivision (qone)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianStirlingGammaLogarithm (source logGammaF logGammaData log_gamma_regular)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "L" => harmonicF
local notation "P" => logGammaF
local notation "C" => constantF

def ratioExponentF : PR 2 := GaussianNamedDifference.nameF P P
def ratioExponentData (a b r : PTm n) : PTm n :=
  GaussianNamedDifference.data (logGammaData (a+b) b) (logGammaData (a+r) b)

theorem ratio_exponent_regular (a b r : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] pointCN ratioExponentF (ratioExponentData a b r) :=
  GaussianNamedDifference.name_regular _ _ _ _
    (log_gamma_regular _ _ (.andI (le_trans ha (le_add_right _ _)) hb))
    (log_gamma_regular _ _ (.andI (le_trans ha (le_add_right _ _)) hb))

theorem ratio_exponent_real (a b r : PTm n) : Γ ⊢[PRAAx] realSamples ratioExponentF (ratioExponentData a b r) :=
  GaussianStirlingNames.add_real _ _ _ _ (GaussianStirlingNames.log_gamma_real (a+b) b)
    (GaussianNamedDampingPowerRealSamples.negative_real _ _ (GaussianStirlingNames.log_gamma_real (a+r) b))

theorem fractional_sum (a D b r s : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (he : Γ ⊢[PRAAx] b ≐ r+s) (ha : Γ ⊢[PRAAx] source a D) :
    Γ ⊢[PRAAx] crossEquivalent (addF L L) H (addData (fractionalData r b a D) (fractionalData s b a D)) (hd a D) := by
  let u := fraction r b
  let v := fraction s b
  let x := hd a D
  have frac : Γ ⊢[PRAAx] fraction (r+s) b ≐ fraction (b*one) (b*one) :=
    GaussianGammaEulerMidpointLogHeadGap.fraction_congr
      (he.eqSymm.eqTrans (by ipra_ring)) (by ipra_ring)
  have e : Γ ⊢[PRAAx] GaussianRationalHorner.qadd u v ≐ qone :=
    (GaussianStirlingOddCoefficients.fraction_add_same r s b hb).eqTrans (frac.eqTrans
      ((GaussianCompactRiemannSplit.fraction_cancel b one one hb (le_refl one)).eqTrans
        GaussianGammaEulerDenominator.natural_one))
  have hu := constant_regular (Γ := Γ) u
  have hv := constant_regular (Γ := Γ) v
  have hx := GaussianHarmonicLogarithmName.name_regular a D ha
  have split := GaussianNameRingLaws.right_distributive C C H u v x hu hv hx
  have ce := cross_trans _ _ _ _ _ _ (constant_sum u v qone e) (GaussianNameRingLaws.constant_one_cross x)
  have lowered := GaussianGammaAdjacentCutoff.multiply_cross (addF C C) oneF H H (addData u v) x x x
    (add_fast _ _ _ _ hu hv) (one_fast _) hx hx ce (cross_refl _ _ hx)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split)
    (cross_trans _ _ _ _ _ _ lowered (multiply_one_left H x hx))

theorem fractional_mono (a d D r b : PTm n) (ha : Γ ⊢[PRAAx] le one a)
    (hD : Γ ⊢[PRAAx] le one D) (had : Γ ⊢[PRAAx] le a d) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realOrder L L (fractionalData r b a D) (fractionalData r b d D) := by
  let J := GaussianPositiveRationalLogarithm.logF
  let jd (x : PTm n) := GaussianPositiveRationalLogarithm.data x D
  have hA : Γ ⊢[PRAAx] source a D := .andI ha hD
  have hB : Γ ⊢[PRAAx] source d D := .andI (le_trans ha had) hD
  have base := GaussianPositiveRationalLogarithmOrder.logarithm_order a D d D hA hB (le_congr (.eqRefl _) (mul_comm d D) (mul_le_mul_right D had))
  have lift := GaussianNamedRealOrderTransport.transport H J J H (hd a D) (jd a) (jd d) (hd d D)
    (cross_symm _ _ _ _ (GaussianHarmonicLogarithmName.cross_original a D hA))
    (GaussianHarmonicLogarithmName.cross_original d D hB) base
  have scaled := GaussianNamedNaturalScaleOrder.preserve_order H H r (hd a D) (hd d D)
    (GaussianHarmonicLogarithmName.name_regular a D hA) (GaussianHarmonicLogarithmName.name_regular d D hB) lift
  have original := GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (scaled_fractional r b a D hb hA) (cross_symm _ _ _ _ (scaled_fractional r b d D hb hB)) scaled
  exact GaussianNamedNaturalScaleOrder.reflect_order L L b _ _ hb
    (fractional_regular r b a D hA) (fractional_regular r b d D hB) original

theorem lower (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] strictOrder L ratioExponentF (fractionalData s b a b) (ratioExponentData a b r) := by
  let x := logGammaData a b
  let y := logGammaData (a+r) b
  let z := logGammaData (a+b) b
  let d := fractionalData r b a b
  let c := fractionalData s b a b
  have hA : Γ ⊢[PRAAx] source a b := .andI ha hb
  have hY : Γ ⊢[PRAAx] source (a+r) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hZ : Γ ⊢[PRAAx] source (a+b) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hx := log_gamma_regular a b hA
  have hy := log_gamma_regular (a+r) b hY
  have hz := log_gamma_regular (a+b) b hZ
  have hc := fractional_regular s b a b hA
  have hd' := fractional_regular r b a b hA
  have plus := GaussianNamedStrictOrderDifference.add_left P (addF L P) L y (addData d x) c
    hy (add_fast _ _ _ _ hd' hx) hc (GaussianGammaRationalUnscaledChord.chord a b r s ha hb hr hs he)
  have regroup := cross_symm _ _ _ _ (add_associative L L P c d x hc hd' hx)
  have replace := add_cross (addF L L) H P P (addData c d) (hd a b) x x (add_fast _ _ _ _ hc hd')
    (GaussianHarmonicLogarithmName.name_regular a b hA) hx hx
    (fractional_sum a b b s r hb (he.eqTrans (add_comm _ _)) hA) (cross_refl _ _ hx)
  have rec' := cross_symm _ _ _ _ (GaussianStirlingGammaLogShift.log_gamma_increment a b hA)
  have h := strict_transport _ _ _ _ _ _ _ _
    (cross_refl _ _ (add_fast _ _ _ _ hc hy))
    (cross_trans _ _ _ _ _ _ regroup (cross_trans _ _ _ _ _ _ replace rec')) plus
  exact GaussianNamedStrictOrderDifference.lt_difference L P P c z y hc hz hy h

theorem upper_at_step (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] strictOrder ratioExponentF L (ratioExponentData a b r) (fractionalData s b (a+r) b) := by
  have hY : Γ ⊢[PRAAx] source (a+r) b := .andI (le_trans ha (le_add_right _ _)) hb
  have hZ : Γ ⊢[PRAAx] source (a+b) b := .andI (le_trans ha (le_add_right _ _)) hb
  exact GaussianNamedStrictOrderDifference.difference_lt P L P _ _ _
    (log_gamma_regular _ _ hZ) (fractional_regular _ _ _ _ hY) (log_gamma_regular _ _ hY)
    (GaussianGammaRationalUnscaledChord.complementary_chord a b r s ha hb hr hs he)

theorem upper (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] strictOrder ratioExponentF L (ratioExponentData a b r) (fractionalData s b (a+b) b) := by
  have h : Γ ⊢[PRAAx] le (a+r) (a+b) :=
    le_congr (by ipra_ring) ((by ipra_ring : Γ ⊢[PRAAx] r+s+a ≐ a+(r+s)).eqTrans
      (congrAdd (.eqRefl _) he.eqSymm)) (add_le_add_right a (le_add_right r s))
  exact GaussianNamedStrictOrderDifference.trans_weak _ _ _ _ _ _ (upper_at_step a b r s ha hb hr hs he)
    (fractional_mono (a+r) (a+b) b s b (le_trans ha (le_add_right _ _)) hb h hb)

end LeanProofs.IPRA.Analysis.GaussianGammaRationalLogGautschi
