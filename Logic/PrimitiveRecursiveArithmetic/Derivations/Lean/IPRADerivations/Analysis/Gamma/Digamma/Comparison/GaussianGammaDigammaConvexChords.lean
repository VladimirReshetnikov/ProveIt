import IPRADerivations.Analysis.Gamma.Digamma.Derivative.GaussianGammaDigammaStep
import IPRADerivations.Analysis.Stirling.GammaIncrements.GaussianStirlingGammaFractionalIncrementObservations

/-!
# One-unit convex chords at native rational Gamma arguments

A positive step 1/D based at x lies below the chord toward x+1.
At x>1 it also lies above the chord from x−1. These comparisons hold
between the original positive-rational log Gamma names.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaConvexChords

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (pos_of_one_le)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaDigammaStep (neighborNumerator neighborDenominator neighbor_source)
open GaussianGammaEulerRationalHeadConvexity (weight barycenter)
open GaussianNameArithmetic (addF addData)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianNamedGammaHalfShift (add_cross)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNaturalScaleProductName (productF productData)
open GaussianRationalHorner (positive_product)
open GaussianStirlingGammaFractionalIncrementConvexity (gamma_rescale_from scaled_regular scale_cross)
open GaussianStirlingGammaLogarithm (source source_shift logGammaF logGammaData log_gamma_regular)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "G" => productF logGammaF
local notation "gd" => productData logGammaF
local notation "lg" => logGammaData

def forwardData (a b D : PTm n) : PTm n := lg (neighborNumerator a b D) (neighborDenominator b D)
def upperWeighted (a b D : PTm n) : Fm PTm n :=
  realOrder G (addF G G) (gd D (forwardData a b D))
    (addData (gd one (lg (a+b) b)) (gd (pred D) (lg a b)))
def lowerWeighted (c b D : PTm n) : Fm PTm n :=
  realOrder G (addF G G) (gd (one+D) (lg (c+b) b))
    (addData (gd one (lg c b)) (gd D (forwardData (c+b) b D)))

set_option maxHeartbeats 800000 in
theorem weighted_upper (a b D : PTm n) (hs : Γ ⊢[PRAAx] source a b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] upperWeighted a b D := by
  let u := D*(a+b)
  let v := D*a
  let B := neighborDenominator b D
  let h := neighborNumerator a b D
  let s := pred D
  let w := weight zero s
  let z := barycenter u v zero s
  have hwb : Γ ⊢[PRAAx] le one B := positive_product _ _ hs.andE₂ hD
  have hu : Γ ⊢[PRAAx] le one u := positive_product _ _ hD (source_shift a b hs).andE₁
  have hv : Γ ⊢[PRAAx] le one v := positive_product _ _ hD hs.andE₁
  have hz : Γ ⊢[PRAAx] le one z :=
    le_trans (positive_product _ _ (le_refl one) hu) (le_add_right _ _)
  have hw : Γ ⊢[PRAAx] le one w := zero_lt_succ _
  have hwB := positive_product _ _ hw hwb
  have eq : Γ ⊢[PRAAx] w ≐ D := by
    have he := natEq (pos_of_one_le hD)
    unfold w weight s
    apply deriveNat
    ipra_simps
    linear_combination -he
  have ez : Γ ⊢[PRAAx] z ≐ D*h := by
    have he := natEq (pos_of_one_le hD)
    unfold z barycenter u v s h neighborNumerator
    apply deriveNat
    ipra_simps
    linear_combination -(𝔞 D*𝔞 a)*he
  have c := gamma_rescale_from z (w*B) h B D (neighbor_source a b D hs hD) hD ez (congrMul eq (.eqRefl _))
  have l := gamma_rescale_from u B (a+b) b D (source_shift a b hs) hD (.eqRefl _) (by unfold B neighborDenominator; ipra_ring)
  have r := gamma_rescale_from v B a b D hs hD (.eqRefl _) (by unfold B neighborDenominator; ipra_ring)
  have eCenter := scale_cross w D (lg z (w*B)) (forwardData a b D) eq
    (log_gamma_regular z (w*B) (.andI hz hwB)) (log_gamma_regular h B (neighbor_source a b D hs hD)) c
  have eLeft := scale_cross one one (lg u B) (lg (a+b) b) (.eqRefl _)
    (log_gamma_regular u B (.andI hu hwb)) (log_gamma_regular _ _ (source_shift a b hs)) l
  have eRight := scale_cross s s (lg v B) (lg a b) (.eqRefl _)
    (log_gamma_regular v B (.andI hv hwb)) (log_gamma_regular a b hs) r
  have eSum := add_cross G G G G (gd one (lg u B)) (gd one (lg (a+b) b)) (gd s (lg v B)) (gd s (lg a b))
    (scaled_regular _ _ (log_gamma_regular u B (.andI hu hwb)))
    (scaled_regular _ _ (log_gamma_regular _ _ (source_shift a b hs)))
    (scaled_regular _ _ (log_gamma_regular v B (.andI hv hwb)))
    (scaled_regular _ _ (log_gamma_regular a b hs)) eLeft eRight
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ eCenter) eSum
    (GaussianGammaNativeLogConvexity.weighted_convexity u v B zero s hu hv hwb)

set_option maxHeartbeats 800000 in
theorem weighted_lower (c b D : PTm n) (hs : Γ ⊢[PRAAx] source c b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] lowerWeighted c b D := by
  let a := c+b
  let u := D*c
  let v := neighborNumerator a b D
  let B := neighborDenominator b D
  let w := weight zero D
  let z := barycenter u v zero D
  have ha := source_shift c b hs
  have hv := neighbor_source a b D ha hD
  have hb : Γ ⊢[PRAAx] le one B := hv.andE₂
  have hu : Γ ⊢[PRAAx] le one u := positive_product _ _ hD hs.andE₁
  have hz : Γ ⊢[PRAAx] le one z :=
    le_trans (positive_product _ _ (le_refl one) hu) (le_add_right _ _)
  have hw : Γ ⊢[PRAAx] le one w := zero_lt_succ _
  have hwB := positive_product _ _ hw hb
  have eq : Γ ⊢[PRAAx] w ≐ one+D := by unfold w weight; ipra_ring
  have ez : Γ ⊢[PRAAx] z ≐ (w*D)*a := by
    unfold z barycenter u v w weight a neighborNumerator
    ipra_ring
  have ed : Γ ⊢[PRAAx] w*B ≐ (w*D)*b := by unfold B neighborDenominator; ipra_ring
  have f := gamma_rescale_from z (w*B) a b (w*D) ha (positive_product _ _ hw hD) ez ed
  have l := gamma_rescale_from u B c b D hs hD (.eqRefl _) (by unfold B neighborDenominator; ipra_ring)
  have eCenter := scale_cross w (one+D) (lg z (w*B)) (lg a b) eq
    (log_gamma_regular z (w*B) (.andI hz hwB)) (log_gamma_regular a b ha) f
  have eLeft := scale_cross one one (lg u B) (lg c b) (.eqRefl _)
    (log_gamma_regular u B (.andI hu hb)) (log_gamma_regular c b hs) l
  have rv := scaled_regular D (lg v B) (log_gamma_regular v B hv)
  have eSum := add_cross G G G G (gd one (lg u B)) (gd one (lg c b)) (gd D (lg v B)) (gd D (lg v B))
    (scaled_regular _ _ (log_gamma_regular u B (.andI hu hb)))
    (scaled_regular _ _ (log_gamma_regular c b hs)) rv rv eLeft (cross_refl _ _ rv)
  exact GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _
    (cross_symm _ _ _ _ eCenter) eSum
    (GaussianGammaNativeLogConvexity.weighted_convexity u v B zero D hu hv.andE₁ hb)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaConvexChords
