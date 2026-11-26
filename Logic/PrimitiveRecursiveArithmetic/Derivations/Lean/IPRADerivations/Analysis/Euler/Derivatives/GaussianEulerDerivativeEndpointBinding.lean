import IPRADerivations.Analysis.Euler.Derivatives.GaussianEulerDerivativeCommonInterval
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicContinuity
import IPRADerivations.Analysis.Euler.Logarithms.GaussianEulerLogarithmicImproperInputProperness

/-!
# Original endpoint observations at the compact derivative path

The left endpoint is the original input with radius R and margin 1/A.
The right endpoint uses the literal shifted numerator and denominator B*D
with the enlarged certificate. Neither is identified with a raw path
encoding. Instead, exact equality after rational normalization transports
the improper observers before applying the common compact cutoff estimate.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDerivativeEndpointBinding

open_ipra
open GaussianEulerDerivativeCommonInterval (compactData improperData)
open GaussianEulerDerivativeParameterPath (point numerator denominator)
open GaussianEulerParameterExponentialIncrement (shifted)
open GaussianRationalHorner (ofGaussian positive_product)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNamedInverseRate (independentRate rate_at rateNumerator rateDenominator denominator_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "I" => GaussianEulerLogarithmicImproperName.nameF
local notation "C" => GaussianEulerLogarithmicIntervalName.nameF
local notation "idata" => GaussianEulerLogarithmicImproperName.data
local notation "ordinary" => GaussianEulerLowerPowerCoefficients.source
local notation "pathSource" => GaussianEulerDerivativeParameterPath.source
local notation "source" => GaussianEulerLogarithmicContinuity.source

private theorem diagonal (t r s j z R B A h D N i w S F V : PTm n)
    (hs : Γ ⊢[PRAAx] pathSource z R B A h D) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (hw : Γ ⊢[PRAAx] ordinary w S F V) (he : Γ ⊢[PRAAx] ofGaussian w F ≐ point z B h D N i) :
    Γ ⊢[PRAAx] distanceBounded (ap2 I t (idata j w S F V)) (ap2 C t (compactData r s j j z R B A h D N i))
      (GaussianNamedLipschitzRate.diagonalNumerator two (unit (r+num 6)) (num 4) t) (unit (r+num 6)*unit t) := by
  let e := unit (r+num 6)
  let u := unit t
  let q := e*u
  have path := GaussianEulerDerivativeParameterPath.path_source z R B A h D N i hs hN hi
  have eq := GaussianEulerLogarithmicImproperInputProperness.original_observations t t j w
    (numerator z B h D N i) S (R+one) F (denominator B D N) V (two*A) (.andI hw (.andI path he))
  have cut := GaussianEulerDerivativeCommonInterval.base_observations t t r s j z R B A h D N i hs hN hi
  have hq : Γ ⊢[PRAAx] le one q := positive_product _ _ (unit_positive _) (unit_positive _)
  have first := distance_radius_mono _ _ _ _ (two*e) q (positive_product _ _ (unit_positive t) (unit_positive t)) hq
    (le_of_eq_add (d := zero) (by dsimp only [e,u,q]; ipra_ring)) eq
  have second := distance_radius_mono _ _ _ _ (two*u+two*e) q (denominator_positive e t t (unit_positive _)) hq
    (le_of_eq_add (d := zero) (by dsimp only [rateNumerator,rateDenominator,e,u,q]; ipra_ring)) cut
  exact distance_congr (.eqRefl _) (.eqRefl _)
    (by dsimp only [GaussianNamedLipschitzRate.diagonalNumerator,e,u]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hq first second)

theorem original_endpoint_rate (r s j z R B A h D N i w S F V : PTm n)
    (hs : Γ ⊢[PRAAx] pathSource z R B A h D) (hN : Γ ⊢[PRAAx] le one N) (hi : Γ ⊢[PRAAx] le i N)
    (hw : Γ ⊢[PRAAx] ordinary w S F V) (he : Γ ⊢[PRAAx] ofGaussian w F ≐ point z B h D N i) :
    Γ ⊢[PRAAx] independentRate I C (idata j w S F V) (compactData r s j j z R B A h D N i) two (unit (r+num 6)) := by
  have cg := GaussianEulerDerivativeCommonInterval.interval_source r s j z R B A h D N i hs hN hi
  have cn : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN C (compactData r s j j z R B A h D N i) :=
    GaussianEulerLogarithmicIntervalName.name_regular j (numerator z B h D N i) (R+one) (denominator B D N) one
      (GaussianEulerDerivativeCommonInterval.intervalWidth r s j R A)
      (GaussianEulerDerivativeCommonInterval.intervalDen r s j R A)
      (GaussianEulerDerivativeCommonInterval.intervalTop r s j R A) cg
  apply GaussianNamedLipschitzRate.independent_rate I C _ _ two (unit (r+num 6)) (num 4)
    (unit_positive _) (GaussianEulerLogarithmicImproperName.name_regular j w S F V hw) cn
  refine .allI ?_
  let sh (v : PTm n) := Syn.shift v
  have hss : Γ.map Fm.shift ⊢[PRAAx] pathSource (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) :=
    by simpa [Fm.shift,Syn.shift,sh] using hs.shift
  have hns : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,one] using hN.shift
  have his : Γ.map Fm.shift ⊢[PRAAx] le (sh i) (sh N) := by simpa [Fm.shift,Syn.shift,sh] using hi.shift
  have hws : Γ.map Fm.shift ⊢[PRAAx] ordinary (sh w) (sh S) (sh F) (sh V) :=
    by simpa [Fm.shift,Syn.shift,sh] using hw.shift
  have hes : Γ.map Fm.shift ⊢[PRAAx] ofGaussian (sh w) (sh F) ≐ point (sh z) (sh B) (sh h) (sh D) (sh N) (sh i) :=
    by simpa [Fm.shift,Syn.shift,sh] using he.shift
  simpa [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianNamedLipschitzRate.diagonalDenominator,Syn.shift,sh,one,two,
    LeanProofs.IPRA.PTm.subst_num] using
    diagonal (var 0) (sh r) (sh s) (sh j) (sh z) (sh R) (sh B) (sh A) (sh h) (sh D) (sh N) (sh i)
      (sh w) (sh S) (sh F) (sh V) hss hns his hws hes

theorem original_left_rate (r s u j z R B A h D N : PTm n)
    (hs : Γ ⊢[PRAAx] source u (succ j) z R B A h D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    independentRate I C (idata j z R B A) (compactData r s j j z R B A h D N zero) two (unit (r+num 6)) := by
  have hp := GaussianEulerLogarithmicContinuity.path_source u (succ j) z R B A h D hs
  have he := GaussianEulerDerivativeParameterPath.point_zero z B h D N hs.andE₁.andE₂.andE₁.andE₁ hs.andE₂.andE₁ hN
  exact original_endpoint_rate r s j z R B A h D N zero z R B A hp hN (zero_le _) hs.andE₁ he.eqSymm

theorem original_right_rate (r s u j z R B A h D N : PTm n)
    (hs : Γ ⊢[PRAAx] source u (succ j) z R B A h D) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    independentRate I C (idata j (shifted z B h D) (R+one) (B*D) (two*A))
      (compactData r s j j z R B A h D N N) two (unit (r+num 6)) := by
  have hp := GaussianEulerLogarithmicContinuity.path_source u (succ j) z R B A h D hs
  have he := GaussianEulerDerivativeParameterPath.point_last z B h D N hs.andE₁.andE₂.andE₁.andE₁ hs.andE₂.andE₁ hN
  exact original_endpoint_rate r s j z R B A h D N N (shifted z B h D) (R+one) (B*D) (two*A) hp hN (le_refl _)
    (GaussianEulerLogarithmicContinuity.shifted_certificate u (succ j) z R B A h D hs) he.eqSymm

theorem actual_original_logarithmic_derivative_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 11
    ((source (var 2) (succ (var 3)) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⋏ le one (var 10)) ⟶
      (independentRate I C (idata (var 3) (var 4) (var 5) (var 6) (var 7))
        (compactData (var 0) (var 1) (var 3) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) zero)
        two (unit (var 0+num 6)) ⋏
       independentRate I C (idata (var 3) (shifted (var 4) (var 6) (var 8) (var 9)) (var 5+one) (var 6*var 9) (two*var 7))
        (compactData (var 0) (var 1) (var 3) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 10))
        two (unit (var 0+num 6)))) :=
  closeUniv 11 (.impI (.andI (original_left_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (original_right_rate _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianEulerDerivativeEndpointBinding
