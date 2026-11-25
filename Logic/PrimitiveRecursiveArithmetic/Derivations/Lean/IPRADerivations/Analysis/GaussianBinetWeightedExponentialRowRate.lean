import IPRADerivations.Analysis.GaussianBinetWeightedExponentialGrid
import IPRADerivations.Analysis.GaussianSignedNameExponentialOrder
import IPRADerivations.Analysis.GaussianNamedAddRate

/-!
# Uniform variation of the original weighted Binet rows

On the unit tag interval a time parameter bounded by T sends every
decay argument into a fixed radius T. The weighted decay observations
have a uniform tag modulus including zero time and the zero tag.
-/

set_option autoImplicit false
set_option maxHeartbeats 620000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialRowRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetWeightedExponentialAlgebra (tagWeight)
open GaussianBinetWeightedExponentialGrid (rowValue zero_observation)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEulerDecayMesh (observation observation_numerator_congr)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameEquivalence (cross_refl)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRadiusExponentialLipschitzRate (factor)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_negative qone_bounded)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (pred num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def gain (T : PTm n) : PTm n := two*(factor T*T)+num 3
def numerator (p q T H D : PTm n) : PTm n := gain T*H*unit p*unit q+two*D*(unit p+unit q)

@[simp] theorem subst_gain {m : ℕ} (σ : Fin n → PTm m) (T : PTm n) :
    Syn.subst σ (gain T) = gain (Syn.subst σ T) := by simp [gain,two]
@[simp] theorem subst_numerator {m : ℕ} (σ : Fin n → PTm m) (p q T H D : PTm n) :
    Syn.subst σ (numerator p q T H D) =
      numerator (Syn.subst σ p) (Syn.subst σ q) (Syn.subst σ T) (Syn.subst σ H) (Syn.subst σ D) := by
  simp [numerator,two]

private theorem weight_bound (i I : PTm n) (hI : Γ ⊢[PRAAx] le one I) (hi : Γ ⊢[PRAAx] le i I) :
    Γ ⊢[PRAAx] bounded (tagWeight i I) two one := by
  have half := GaussianEulerExponentCompactBounds.fraction_bound (Γ := Γ) one two one (le_succ_self one)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (le_succ_self one))
  have tag := GaussianEulerExponentCompactBounds.fraction_bound i I one hI
    (le_congr (.eqRefl _) (one_mul _).eqSymm hi)
  exact bound_congr (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianRationalPowerDifference.bounded_sum_same _ _ _ _ _ (le_refl one) half
      (bounded_negative _ _ _ (le_refl one) tag))

private theorem old_decay_bound (a b p : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (observation a b p) (num 3) one := by
  refine .orE (zero_or_succ a) ?_ ?_
  · exact bound_congr ((observation_numerator_congr a zero b p Prf.hyp0).eqTrans
      (zero_observation b p hb.wk)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _ (le_refl one) (le_refl one)
        (by ipra_le 2) qone_bounded)
  · have ha : (a ≐ succ (pred a))::Γ ⊢[PRAAx] le one a :=
      le_congr (.eqRefl _) Prf.hyp0.eqSymm (zero_lt_succ _)
    exact bound_congr (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (.eqRefl _)
      (GaussianEulerDecayIncrement.decay_observation_uniform_bound a b p ha hb.wk)

private theorem decay_exponent_bound (a b i I T : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (ht : Γ ⊢[PRAAx] le a (T*b)) (hI : Γ ⊢[PRAAx] le one I) (hi : Γ ⊢[PRAAx] le i I) :
    Γ ⊢[PRAAx] bounded (decayPoint (a*i) (b*I)) T one := by
  have top := mul_le_mul_right i ht
  have tag := mul_le_mul_right (T*b) hi
  have hn : Γ ⊢[PRAAx] le (a*i) (T*(b*I)) :=
    le_trans top (le_congr (by ipra_ring) (by ipra_ring) tag)
  exact bounded_negative _ _ one (le_refl one)
    (GaussianEulerExponentCompactBounds.fraction_bound _ _ _ (positive_product _ _ hb hI) hn)

private theorem original_radius (z T : PTm n) (h : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input constantF T z) :
    Γ ⊢[PRAAx] GaussianNameEquivalence.crossEquivalent decayF decayF
      (GaussianRadiusExponentialName.data (GaussianNameBounds.U constantF z) z) (GaussianRadiusExponentialName.data T z) :=
  GaussianExponentialRadiusIndependence.independent_radii_proper constantF constantF
    (GaussianNameBounds.U constantF z) T z z
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (constant_regular _)) h (cross_refl _ _ (constant_regular _))

theorem decay_rate (a b i I j J T H D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b))
    (hI : Γ ⊢[PRAAx] le one I) (hi : Γ ⊢[PRAAx] le i I)
    (hJ : Γ ⊢[PRAAx] le one J) (hj : Γ ⊢[PRAAx] le j J)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded (fraction i I) (fraction j J) H D) :
    Γ ⊢[PRAAx] independentRate decayF decayF (decayData (a*i) (b*I)) (decayData (a*j) (b*J)) (factor T*(T*H)) D := by
  let x := decayPoint (a*i) (b*I)
  let y := decayPoint (a*j) (b*J)
  have ha := GaussianEulerExponentCompactBounds.fraction_bound a b T hb ht
  have d := GaussianApproximateInverseDistance.multiply_distance (fraction a b) (fraction i I) (fraction j J) T H D hD ha h
  have ex := GaussianEulerDampedTimeRate.fraction_product a b i I hb hI
  have ey := GaussianEulerDampedTimeRate.fraction_product a b j J hb hJ
  have neg := GaussianNamedDifference.negative_distance _ _ _ _ hD
    (distance_congr ex ey (.eqRefl _) (.eqRefl _) d)
  have hx := GaussianSignedNameExponentialOrder.constant_input x T (decay_exponent_bound a b i I T hb ht hI hi)
  have hy := GaussianSignedNameExponentialOrder.constant_input y T (decay_exponent_bound a b j J T hb ht hJ hj)
  have rate := GaussianNamedAddRate.constant_rate x y (T*H) D hD neg
  have common := GaussianRadiusExponentialLipschitzRate.independent_rate constantF constantF T x y
    (T*H) D (.andI hD (.andI hx (.andI hy rate)))
  exact GaussianNamedRateTransport.transport _ _ decayF decayF _ _ _ _ _ D hD common
    (original_radius x T hx) (original_radius y T hy)

theorem row_error (p q a b i I j J T H D : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (ht : Γ ⊢[PRAAx] le a (T*b))
    (hI : Γ ⊢[PRAAx] le one I) (hi : Γ ⊢[PRAAx] le i I)
    (hJ : Γ ⊢[PRAAx] le one J) (hj : Γ ⊢[PRAAx] le j J)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded (fraction i I) (fraction j J) H D) :
    Γ ⊢[PRAAx] distanceBounded (rowValue p a b i I) (rowValue q a b j J)
      (numerator p q T H D) (rateDenominator D p q) := by
  let u := observation (a*i) (b*I) p
  let v := observation (a*j) (b*J) q
  let M := rateDenominator D p q
  have hM := GaussianNamedInverseRate.denominator_positive D p q hD
  have weight := weight_bound i I hI hi
  have d : Γ ⊢[PRAAx] distanceBounded u v (rateNumerator (factor T*(T*H)) D p q) M :=
    GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (decay_rate a b i I j J T H D hb ht hI hi hJ hj hD h)
  have first := GaussianApproximateInverseDistance.multiply_distance _ _ _ _ _ _ hM weight d
  have wd : Γ ⊢[PRAAx] distanceBounded (tagWeight i I) (tagWeight j J) H D :=
    GaussianNameRingLaws.sum_right_error _ _ _ _ _ hD (GaussianNamedDifference.negative_distance _ _ _ _ hD h)
  have scaled := distance_radius_mono _ _ _ _ (H*unit p*unit q) M hD hM
    (le_of_eq_add (d := zero) (by dsimp only [M,rateDenominator]; ipra_ring)) wd
  have second := GaussianApproximateInverseDistance.multiply_distance v _ _ (num 3) _ M hM
    (old_decay_bound (a*j) (b*J) q (positive_product _ _ hb hJ)) scaled
  have next := distance_congr (GaussianRationalPowerAlgebra.qmul_commutative _ _)
    (GaussianRationalPowerAlgebra.qmul_commutative _ _) (.eqRefl _) (.eqRefl _) second
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [numerator,gain,rateNumerator]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hM first next)

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialRowRate
