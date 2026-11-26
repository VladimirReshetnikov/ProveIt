import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetStirlingRemainder
import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneLogarithmCompactBound
import IPRADerivations.Analysis.Logarithm.GaussianRightHalfPlaneLogarithmNamed
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.GaussianLogGammaEulerNamed
import IPRADerivations.Analysis.Euler.PowerScaling.GaussianEulerNamedPowerScalingPowerFrozen
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedAddRate

/-!
# Uniform parameter variation of the original Stirling remainder

The signed rational charts share one disk and inverse real margin.
The rate combines the actual logarithm and log-Gamma programs, the
literal argument offset, and the unchanged named Stirling constant.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetStirlingRemainderRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetStirlingRemainder (offset weightedF weightedData coreF coreData)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRightHalfPlaneSigned (certificate denominator imagNumerator point realNumerator sign point_bound)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded qnegative)
open GaussianRationalReciprocal (bounded_negative)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "S" => GaussianBinetStirlingRemainder.nameF
local notation "sd" => GaussianBinetStirlingRemainder.data
local notation "L" => GaussianRightHalfPlaneLogarithm.nameF
local notation "ld" => GaussianRightHalfPlaneLogarithmNamed.pointData
local notation "G" => GaussianLogGammaEulerCofinal.nameF
local notation "gd" => GaussianLogGammaEulerNamed.pointData
local notation "C" => GaussianStirlingConstant.nameF
local notation "cd" => GaussianStirlingConstant.nameData
local notation "Diff" => GaussianNamedDifference.nameF
local notation "dd" => GaussianNamedDifference.data
local notation "lc" => GaussianRightHalfPlaneLogarithmNamed.coefficient
local notation "gc" => GaussianLogGammaEulerNamed.coefficient
local notation "lr" => GaussianRightHalfPlaneLogarithmCompactBound.radius
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def pointOffset (q : PTm n) : PTm n := offset (realNumerator q) (imagNumerator q) (denominator q) (sign q)
def pointData (q x : PTm n) : PTm n :=
  sd (realNumerator q) (imagNumerator q) (denominator q) (sign q) x
def productGain (R K : PTm n) : PTm n := lr R K+(R+one)*lc R K
def gain (R K : PTm n) : PTm n := (gc R K+productGain R K)+one

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (R K : PTm n) :
    Syn.subst σ (gain R K) = gain (Syn.subst σ R) (Syn.subst σ K) := by
  simp [gain,productGain,GaussianLogGammaEulerNamed.coefficient,GaussianRightHalfPlaneLogarithmNamed.coefficient,one]

private theorem offset_bound (q R K : PTm n) (hq : Γ ⊢[PRAAx] certificate q R K) :
    Γ ⊢[PRAAx] bounded (pointOffset q) (R+one) one := by
  let h : PTm n := fraction one two
  have b : Γ ⊢[PRAAx] bounded h one one :=
    GaussianEulerExponentCompactBounds.fraction_bound one two one (le_succ_self one)
      (le_congr (.eqRefl _) (one_mul _).eqSymm (le_succ_self one))
  exact GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one) (point_bound q R K hq)
    (bounded_negative _ _ one (le_refl one) b)

theorem independent_rate (x y R K E D w : PTm n)
    (hx : Γ ⊢[PRAAx] certificate x R K) (hy : Γ ⊢[PRAAx] certificate y R K)
    (hD : Γ ⊢[PRAAx] le one D) (small : Γ ⊢[PRAAx] le (gain R K*E) D)
    (near : Γ ⊢[PRAAx] distanceBounded (point x) (point y) E D) :
    Γ ⊢[PRAAx] independentRate S S (pointData x w) (pointData y w) (gain R K*E) D := by
  have logSmall : Γ ⊢[PRAAx] le (lc R K*E) D := le_trans
    (by dsimp only [gain,productGain]; ipra_le 𝔞(gc R K)*𝔞(E)+𝔞(lr R K)*𝔞(E)+
      𝔞(R)*𝔞(lc R K)*𝔞(E)+𝔞(E)) small
  have gammaSmall : Γ ⊢[PRAAx] le (gc R K*E) D := le_trans
    (by dsimp only [gain]; ipra_le 𝔞(productGain R K)*𝔞(E)+𝔞(E)) small
  have hxL := GaussianRightHalfPlaneLogarithm.regular (realNumerator x) (imagNumerator x)
    (denominator x) (sign x) hx.andE₁.andE₁
  have hyL := GaussianRightHalfPlaneLogarithm.regular (realNumerator y) (imagNumerator y)
    (denominator y) (sign y) hy.andE₁.andE₁
  have hxG := GaussianLogGammaEulerCofinal.canonical_regular (realNumerator x) (imagNumerator x)
    (denominator x) (sign x) hx.andE₁.andE₁
  have hyG := GaussianLogGammaEulerCofinal.canonical_regular (realNumerator y) (imagNumerator y)
    (denominator y) (sign y) hy.andE₁.andE₁
  have hxO := constant_regular (Γ := Γ) (pointOffset x)
  have hyO := constant_regular (Γ := Γ) (pointOffset y)
  have ry := GaussianEulerNamedPowerScalingPowerFrozen.constant_bound (pointOffset y) (R+one) (offset_bound y R K hy)
  have rx := GaussianRightHalfPlaneLogarithmCompactBound.samples_bounded (realNumerator x) (imagNumerator x)
    (denominator x) (sign x) R K hx.andE₁ hx.andE₂.andE₁
  have logs := GaussianRightHalfPlaneLogarithmNamed.original_variation x y R K E D hx hy hD logSmall near
  have gamma := GaussianLogGammaEulerNamed.original_variation x y R K E D hx hy hD gammaSmall near
  have edge := GaussianNameRingLaws.sum_left_error (point x) (point y) (qnegative (fraction one two)) E D hD near
  have offsets := GaussianNamedAddRate.constant_rate (pointOffset x) (pointOffset y) E D hD edge
  have arg := GaussianNamedAddRate.constant_rate (point x) (point y) E D hD near
  let wx := weightedData (realNumerator x) (imagNumerator x) (denominator x) (sign x)
  let wy := weightedData (realNumerator y) (imagNumerator y) (denominator y) (sign y)
  have product : Γ ⊢[PRAAx] independentRate weightedF weightedF wx wy (productGain R K*E) D := by
    have raw := GaussianEulerNamedPowerScalingPowerFrozen.multiply_same_denominator constantF L constantF L
      (pointOffset x) (ld x) (pointOffset y) (ld y) E (lc R K*E) D (lr R K) (R+one) hD
      hxO hxL hyO hyL rx ry offsets logs
    exact GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _
      (by dsimp only [productGain]; ipra_ring) (.eqRefl _) raw
  have hWx := GaussianNameArithmetic.multiply_fast constantF L (pointOffset x) (ld x) hxO hxL
  have hWy := GaussianNameArithmetic.multiply_fast constantF L (pointOffset y) (ld y) hyO hyL
  have dx := GaussianNamedDifference.name_regular G weightedF (gd x) wx hxG hWx
  have dy := GaussianNamedDifference.name_regular G weightedF (gd y) wy hyG hWy
  let F := Diff G weightedF
  let a := (gc R K+productGain R K)*E
  have D2 := positive_product _ _ hD hD
  have diff : Γ ⊢[PRAAx] independentRate F F (dd (gd x) wx) (dd (gd y) wy) a D := by
    have raw := GaussianNamedDifferenceRate.original_rate G weightedF G weightedF (gd x) wx (gd y) wy
      (gc R K*E) D (productGain R K*E) D
      (.andI (.andI hD hD) (.andI (.andI hxG hWx) (.andI (.andI hyG hWy) (.andI gamma product))))
    exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ D2 hD
      (le_of_eq_add (d := zero) (by dsimp only [a,GaussianNamedDifferenceRate.leadingNumerator,
        GaussianNamedDifferenceRate.leadingDenominator]; ipra_ring)) raw
  let cx := coreData (realNumerator x) (imagNumerator x) (denominator x) (sign x)
  let cy := coreData (realNumerator y) (imagNumerator y) (denominator y) (sign y)
  have core : Γ ⊢[PRAAx] independentRate coreF coreF cx cy (gain R K*E) D := by
    have raw := GaussianNamedAddRate.independent_rate F constantF F constantF (dd (gd x) wx) (point x)
      (dd (gd y) wy) (point y) a D E D hD hD diff arg
    exact GaussianNamedRateRadius.weaken _ _ _ _ _ _ _ _ D2 hD
      (le_of_eq_add (d := zero) (by dsimp only [a,gain,GaussianNamedRateComposition.leadingNumerator,
        GaussianNamedRateComposition.leadingDenominator]; ipra_ring)) raw
  exact GaussianNamedDifferenceRate.same_right_rate coreF coreF C cx cy (cd w) (gain R K*E) D hD
    (GaussianNameArithmetic.add_fast _ _ _ _ dx (constant_regular _))
    (GaussianNameArithmetic.add_fast _ _ _ _ dy (constant_regular _))
    (GaussianStirlingConstant.name_regular w) core

end LeanProofs.IPRA.Analysis.GaussianBinetStirlingRemainderRate
