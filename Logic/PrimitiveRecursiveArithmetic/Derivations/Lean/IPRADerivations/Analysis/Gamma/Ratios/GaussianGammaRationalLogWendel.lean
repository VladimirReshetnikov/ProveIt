import IPRADerivations.Analysis.Gamma.Ratios.GaussianGammaRationalLogGautschi
import IPRADerivations.Analysis.Euler.HarmonicLogarithms.GaussianHarmonicLogarithmProduct

/-!
# The exact rational Wendel comparison in logarithms

The relative logarithm is `(1-u)log x − (logΓ(x+1) − logΓ(x+u))`.
The two strict Gautschi-side estimates give its exact lower bound
`(1-u)log(x/(x+u))` and upper bound zero.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianGammaRationalLogWendel

open_ipra
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaRationalFractionalChord (harmonicF)
open GaussianGammaRationalUnscaledChord (fractionalData fractional_regular fractional_real)
open GaussianGammaRationalLogGautschi (ratioExponentF ratioExponentData ratio_exponent_regular ratio_exponent_real)
open GaussianNameArithmetic (addF addData add_fast multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans)
open GaussianNameRingLaws (negativeF negativeData negative_fast add_negative zeroF)
open GaussianNamedDifference (name_regular)
open GaussianSignedNameExponentialOrder (realSamples)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianStirlingGammaLogarithm (source)
open GaussianStirlingMultiplicativeBoundsStrictOrder (strictOrder strict_transport)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "H" => GaussianHarmonicLogarithmName.nameF
local notation "hd" => GaussianHarmonicLogarithmName.data
local notation "L" => harmonicF
local notation "C" => constantF
local notation "D" => ratioExponentF

def relativeExponentF : PR 2 := GaussianNamedDifference.nameF L D
def relativeExponentData (a b r s : PTm n) : PTm n :=
  GaussianNamedDifference.data (fractionalData s b a b) (ratioExponentData a b r)

theorem relative_exponent_regular (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] pointCN relativeExponentF (relativeExponentData a b r s) :=
  name_regular _ _ _ _ (fractional_regular s b a b (.andI ha hb)) (ratio_exponent_regular a b r ha hb)

theorem relative_exponent_real (a b r s : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] realSamples relativeExponentF (relativeExponentData a b r s) :=
  GaussianStirlingNames.add_real _ _ _ _ (fractional_real s b a b hb)
    (GaussianNamedDampingPowerRealSamples.negative_real _ _ (ratio_exponent_real a b r))

theorem log_ratio_sum (a j b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hj : Γ ⊢[PRAAx] le one j)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (addF H H) H (addData (hd a j) (hd j b)) (hd a b) := by
  have hs : Γ ⊢[PRAAx] source a b := .andI ha hb
  have left := GaussianHarmonicLogarithmProduct.logarithm_product a j j b (.andI (.andI ha hj) (.andI hj hb))
  have right := GaussianGammaStrongLogConvexityAlgebra.harmonic_rescale a b j hs hj
  have reorder : Γ ⊢[PRAAx] hd (j*a) (j*b) ≐ hd (a*j) (j*b) :=
    congrPairT (mul_comm j a) (.eqRefl (j*b))
  have reordered := GaussianGammaCompactCutoffAlignment.cross_data_congr H H (hd (j*a) (j*b)) (hd (a*j) (j*b))
    (hd a b) (hd a b) reorder (.eqRefl _) right
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ left) reordered

theorem fractional_log_ratio_sum (a j b s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hj : Γ ⊢[PRAAx] le one j)
    (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] crossEquivalent (addF L L) L
      (addData (fractionalData s b a j) (fractionalData s b j b)) (fractionalData s b a b) := by
  let c := fraction s b
  let x := hd a j
  let y := hd j b
  let z := hd a b
  have hc := constant_regular (Γ := Γ) c
  have hx := GaussianHarmonicLogarithmName.name_regular a j (.andI ha hj)
  have hy := GaussianHarmonicLogarithmName.name_regular j b (.andI hj hb)
  have hz := GaussianHarmonicLogarithmName.name_regular a b (.andI ha hb)
  have split := GaussianNameRingLaws.distributive C H H c x y hc hx hy
  have fold := GaussianGammaAdjacentCutoff.multiply_cross C C (addF H H) H c c (addData x y) z
    hc hc (add_fast _ _ _ _ hx hy) hz (cross_refl _ _ hc) (log_ratio_sum a j b ha hj hb)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ split) fold

theorem lower (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] strictOrder L relativeExponentF (fractionalData s b a (a+r)) (relativeExponentData a b r s) := by
  let j := a+r
  let d := ratioExponentData a b r
  let t := fractionalData s b a j
  let u := fractionalData s b j b
  let v := fractionalData s b a b
  have hj : Γ ⊢[PRAAx] le one j := le_trans ha (le_add_right _ _)
  have hD := ratio_exponent_regular a b r ha hb
  have ht := fractional_regular s b a j (.andI ha hj)
  have hu := fractional_regular s b j b (.andI hj hb)
  have hv := fractional_regular s b a b (.andI ha hb)
  have first := GaussianNamedStrictOrderDifference.add_left D L L d u t hD hu ht
    (GaussianGammaRationalLogGautschi.upper_at_step a b r s ha hb hr hs he)
  have second := strict_transport _ _ _ _ _ _ _ _ (cross_refl _ _ (add_fast _ _ _ _ ht hD))
    (fractional_log_ratio_sum a j b s ha hj hb) first
  exact GaussianNamedStrictOrderDifference.lt_difference L L D t v d ht hv hD second

theorem upper (a b r s : PTm n) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hr : Γ ⊢[PRAAx] le one r) (hs : Γ ⊢[PRAAx] le one s) (he : Γ ⊢[PRAAx] b ≐ r+s) :
    Γ ⊢[PRAAx] strictOrder relativeExponentF zeroF (relativeExponentData a b r s) (ratioExponentData a b r) := by
  let d := ratioExponentData a b r
  let v := fractionalData s b a b
  have hD := ratio_exponent_regular a b r ha hb
  have hv := fractional_regular s b a b (.andI ha hb)
  have left := GaussianNamedStrictOrderDifference.add_right L D (negativeF D) v d (negativeData d)
    hv hD (negative_fast D d hD) (GaussianGammaRationalLogGautschi.lower a b r s ha hb hr hs he)
  exact strict_transport _ _ _ _ _ _ _ _ (cross_refl _ _ (name_regular L D v d hv hD)) (add_negative D d hD) left

end LeanProofs.IPRA.Analysis.GaussianGammaRationalLogWendel
