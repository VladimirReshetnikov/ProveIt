import IPRADerivations.Analysis.GaussianEulerPositiveScalingIntegrand
import IPRADerivations.Analysis.GaussianEulerCompactPowerVariation
import IPRADerivations.Analysis.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.GaussianNamedMultiplyRate

/-!
# Actual compact time rates for the damped original Euler client

The power and the decay retain their original names and multiplication
clock. Only the decay argument is multiplied by a positive rational c/d.
A common numerical disk c*T bounds its actual exponential queries;
separate original radii are transported using proved properness.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDampedTimeRate

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (powerF powerData decayF decayData decayPoint)
open GaussianEulerPositiveScalingIntegrand (dampedF dampedData)
open GaussianEulerExponentCompactBounds (source)
open GaussianCompactLogarithmBounds (domain)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def decayRadius (T c : PTm n) : PTm n := c*T
def decayBound (T c : PTm n) : PTm n := GaussianRadiusExponentialLipschitzRate.factor (decayRadius T c)
def decayLipschitz (T c : PTm n) : PTm n := decayBound T c*c
def lipschitz (R E T c _d : PTm n) : PTm n :=
  decayBound T c*GaussianEulerCompactPowerVariation.lipschitz R E T+
    GaussianEulerCompactPowerMajorant.majorant R E T*decayLipschitz T c

def input (z R B E T c d a b u v A D : PTm n) : Fm PTm n :=
  (source z R B E ⋏ (le one c ⋏ le one d)) ⋏
    (domain a b E T ⋏ (domain u v E T ⋏ (le one D ⋏ distanceBounded (fraction a b) (fraction u v) A D)))

@[simp] theorem subst_decayRadius {m : ℕ} (σ : Fin n → PTm m) (T c : PTm n) :
    Syn.subst σ (decayRadius T c) = decayRadius (Syn.subst σ T) (Syn.subst σ c) := by simp [decayRadius]
@[simp] theorem subst_decayBound {m : ℕ} (σ : Fin n → PTm m) (T c : PTm n) :
    Syn.subst σ (decayBound T c) = decayBound (Syn.subst σ T) (Syn.subst σ c) := by simp [decayBound]
@[simp] theorem subst_decayLipschitz {m : ℕ} (σ : Fin n → PTm m) (T c : PTm n) :
    Syn.subst σ (decayLipschitz T c) = decayLipschitz (Syn.subst σ T) (Syn.subst σ c) := by simp [decayLipschitz]
@[simp] theorem subst_lipschitz {m : ℕ} (σ : Fin n → PTm m) (R E T c d : PTm n) :
    Syn.subst σ (lipschitz R E T c d) = lipschitz (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ c) (Syn.subst σ d) := by
  simp [lipschitz,GaussianEulerCompactPowerMajorant.majorant,GaussianEulerCompactPowerMajorant.exponentRadius]
@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (z R B E T c d a b u v A D : PTm n) :
    (input z R B E T c d a b u v A D).subst σ = input (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ c) (Syn.subst σ d) (Syn.subst σ a) (Syn.subst σ b)
      (Syn.subst σ u) (Syn.subst σ v) (Syn.subst σ A) (Syn.subst σ D) := by simp [input]

@[simp] theorem subst_decayData {m : ℕ} (σ : Fin n → PTm m) (a b : PTm n) :
    Syn.subst σ (decayData a b) = decayData (Syn.subst σ a) (Syn.subst σ b) := by
  simp [decayData,GaussianGammaFiniteApproximantName.exponentialInputData]
@[simp] theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m) (R E T : PTm n) :
    Syn.subst σ (GaussianEulerCompactPowerMajorant.majorant R E T) =
      GaussianEulerCompactPowerMajorant.majorant (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) := by
  simp [GaussianEulerCompactPowerMajorant.majorant,GaussianEulerCompactPowerMajorant.exponentRadius]

/-- Exact multiplication of the actual canonical positive fraction codes. -/
theorem fraction_product (c d a b : PTm n) (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) : Γ ⊢[PRAAx]
    qmul (fraction c d) (fraction a b) ≐ fraction (c*a) (d*b) :=
  (GaussianRationalSyntheticDivision.qmul_congr
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point c d hd)
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb)).eqTrans
    ((GaussianDominantPairAlgebra.radius_multiply c d a b hd hb).eqTrans
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point (c*a) (d*b) (positive_product _ _ hd hb)).eqSymm)

theorem scaled_time_distance (c d a b u v A D : PTm n)
    (hd : Γ ⊢[PRAAx] le one d) (hb : Γ ⊢[PRAAx] le one b) (hv : Γ ⊢[PRAAx] le one v)
    (hD : Γ ⊢[PRAAx] le one D) (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction u v) A D) : Γ ⊢[PRAAx]
    distanceBounded (fraction (c*a) (d*b)) (fraction (c*u) (d*v)) (c*A) D := by
  have hscale := GaussianEulerExponentCompactBounds.fraction_bound c d c hd
    (le_congr (one_mul c) (by ipra_ring) (mul_le_mul_right c hd))
  have raw := GaussianApproximateInverseDistance.multiply_distance (fraction c d) (fraction a b) (fraction u v) c A D hD hscale h
  exact distance_congr (fraction_product c d a b hd hb) (fraction_product c d u v hd hv) (.eqRefl _) (.eqRefl _) raw

theorem scaled_decay_bound (T c d a b E : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx] bounded (decayPoint (c*a) (d*b)) (decayRadius T c) one := by
  have first : Γ ⊢[PRAAx] le (c*a) (c*(T*b)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right c ht.andE₂.andE₂)
  have enlarge := mul_le_mul_right (c*(T*b)) hd
  have upper : Γ ⊢[PRAAx] le (c*a) ((c*T)*(d*b)) := le_trans first
    (le_congr (by ipra_ring) (by ipra_ring) enlarge)
  exact GaussianRationalReciprocal.bounded_negative _ _ one (le_refl one)
    (GaussianEulerExponentCompactBounds.fraction_bound _ _ _ (positive_product _ _ hd ht.andE₁.andE₂) upper)

private theorem constant_rate (x y A D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded x y A D) : Γ ⊢[PRAAx] independentRate constantF constantF x y A D := by
  have ds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using hD.shift.shift
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] distanceBounded (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y))
      (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift] using distance_congr
    (constant_at (var 1) (Syn.shift (Syn.shift x))).eqSymm (constant_at (var 0) (Syn.shift (Syn.shift y))).eqSymm
    (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ (rateNumerator (Syn.shift (Syn.shift A)) (Syn.shift (Syn.shift D)) (var 1) (var 0))
      (rateDenominator (Syn.shift (Syn.shift D)) (var 1) (var 0)) ds
      (GaussianNamedInverseRate.denominator_positive _ _ _ ds)
      (le_of_eq_add (d := (Syn.shift (Syn.shift D))*(Syn.shift (Syn.shift D))*(unit (var 1)+unit (var 0)))
        (by unfold rateNumerator rateDenominator; ipra_ring)) hs)

theorem decay_common_input (T c d a b E : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    GaussianRadiusExponentialName.input constantF (decayRadius T c) (decayPoint (c*a) (d*b)) := by
  refine .andI (constant_regular _) (.allI ?_)
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using ht.shift
  simpa only [GaussianRadiusExponentialName.boundedSamples,GaussianEulerIntegrandName.subst_decayPoint,subst_decayRadius,Syn.shift,PTm.subst_mul] using
    GaussianRationalReciprocal.bound_congr (constant_at (var 0) (decayPoint (Syn.shift c*Syn.shift a) (Syn.shift d*Syn.shift b))).eqSymm
      (.eqRefl _) (.eqRefl _) (scaled_decay_bound (Syn.shift T) (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift b) (Syn.shift E) ds ts)

theorem original_decay_rate (T c d a b u v E A D : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] domain a b E T) (hu : Γ ⊢[PRAAx] domain u v E T) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction u v) A D) : Γ ⊢[PRAAx]
    independentRate decayF decayF (decayData (c*a) (d*b)) (decayData (c*u) (d*v)) (decayLipschitz T c*A) D := by
  have left := decay_common_input T c d a b E hd ha
  have right := decay_common_input T c d u v E hd hu
  have rate := constant_rate _ _ (c*A) D hD
    (GaussianEulerExponentCompactBounds.negative_distance _ _ _ _ hD (scaled_time_distance c d a b u v A D hd ha.andE₁.andE₂ hu.andE₁.andE₂ hD h))
  have common := GaussianRadiusExponentialLipschitzRate.independent_rate constantF constantF (decayRadius T c)
    (decayPoint (c*a) (d*b)) (decayPoint (c*u) (d*v)) (c*A) D (.andI hD (.andI left (.andI right rate)))
  have lproper := GaussianExponentialRadiusIndependence.independent_radii_proper constantF constantF
    (GaussianNameBounds.U constantF (decayPoint (c*a) (d*b))) (decayRadius T c)
    (decayPoint (c*a) (d*b)) (decayPoint (c*a) (d*b))
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (constant_regular _)) left
    (GaussianNameEquivalence.cross_refl _ _ (constant_regular _))
  have rproper := GaussianExponentialRadiusIndependence.independent_radii_proper constantF constantF
    (GaussianNameBounds.U constantF (decayPoint (c*u) (d*v))) (decayRadius T c)
    (decayPoint (c*u) (d*v)) (decayPoint (c*u) (d*v))
    (GaussianGammaFiniteApproximantName.exponential_input _ _ (constant_regular _)) right
    (GaussianNameEquivalence.cross_refl _ _ (constant_regular _))
  exact GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _ (by unfold decayLipschitz decayBound; ipra_ring)
    (GaussianNamedRateTransport.transport _ _ decayF decayF _ _ _ _ _ D hD common lproper rproper)

theorem decay_observation_bound (p T c d a b E : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (ap2 decayF p (decayData (c*a) (d*b))) (decayBound T c) one := by
  let r := GaussianNameBounds.U constantF (decayPoint (c*a) (d*b))
  let K := GaussianRadiusExponentialName.index r p
  have raw := GaussianPositiveExponentialMajorant.disk_bound (decayPoint (c*a) (d*b)) (decayRadius T c) K (scaled_decay_bound T c d a b E hd ht)
  have readback : Γ ⊢[PRAAx] ap2 decayF p (decayData (c*a) (d*b)) ≐
      GaussianRationalPolynomialExponential.scalarSum (decayPoint (c*a) (d*b)) K :=
    (GaussianRadiusExponentialName.sample_at constantF r p _).eqTrans
      (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _) (constant_at _ _))
  exact GaussianRationalReciprocal.bound_congr readback.eqSymm (.eqRefl _) (.eqRefl _) raw

theorem decay_sample_bound (T c d a b E : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    GaussianNamedMultiplyRate.sampleBound decayF (decayData (c*a) (d*b)) (decayBound T c) := by
  have ds : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift d) := by simpa [Fm.shift,Syn.shift] using hd.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using ht.shift
  refine .allI ?_
  simpa only [GaussianNamedMultiplyRate.sampleBound,subst_decayData,subst_decayBound,Syn.shift,PTm.subst_mul] using
    decay_observation_bound (var 0) (Syn.shift T) (Syn.shift c) (Syn.shift d) (Syn.shift a) (Syn.shift b) (Syn.shift E) ds ts

theorem power_sample_bound (z R B E T a b : PTm n) (hz : Γ ⊢[PRAAx] source z R B E) (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    GaussianNamedMultiplyRate.sampleBound powerF (powerData z B a b) (GaussianEulerCompactPowerMajorant.majorant R E T) := by
  have zs : Γ.map Fm.shift ⊢[PRAAx] source (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) := by simpa [Fm.shift,Syn.shift] using hz.shift
  have ts : Γ.map Fm.shift ⊢[PRAAx] domain (Syn.shift a) (Syn.shift b) (Syn.shift E) (Syn.shift T) := by simpa [Fm.shift,Syn.shift] using ht.shift
  refine .allI ?_
  simpa only [GaussianNamedMultiplyRate.sampleBound,GaussianEulerIntegrandName.subst_powerData,subst_majorant,Syn.shift] using
    GaussianEulerCompactPowerMajorant.original_power_observation (var 0) (Syn.shift z) (Syn.shift R) (Syn.shift B) (Syn.shift E) (Syn.shift T) (Syn.shift a) (Syn.shift b) zs ts

private theorem cancel_rate_denominator (F G : PR 2) (x y K D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] independentRate F G x y (K*D) (D*D)) : Γ ⊢[PRAAx] independentRate F G x y K D := by
  have ds : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] le one (Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using hD.shift.shift
  have hs : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] independentRate F G (Syn.shift (Syn.shift x)) (Syn.shift (Syn.shift y))
      (Syn.shift (Syn.shift K)*Syn.shift (Syn.shift D)) (Syn.shift (Syn.shift D)*Syn.shift (Syn.shift D)) := by simpa [Fm.shift,Syn.shift] using h.shift.shift
  refine .allI (.allI ?_)
  simpa only [independentRate,Syn.shift] using
    (distance_radius_mono _ _ _ _ (rateNumerator (Syn.shift (Syn.shift K)) (Syn.shift (Syn.shift D)) (var 1) (var 0))
      (rateDenominator (Syn.shift (Syn.shift D)) (var 1) (var 0))
      (GaussianNamedInverseRate.denominator_positive _ _ _ (positive_product _ _ ds ds))
      (GaussianNamedInverseRate.denominator_positive _ _ _ ds)
      (le_of_eq_add (d := zero) (by unfold rateNumerator rateDenominator; ipra_ring))
      (GaussianNamedInverseRate.rate_at _ _ _ _ _ _ (var 1) (var 0) hs))

theorem original_rate (z R B E T c d a b u v A D : PTm n) (h : Γ ⊢[PRAAx] input z R B E T c d a b u v A D) : Γ ⊢[PRAAx]
    independentRate dampedF dampedF (dampedData z B a b c d) (dampedData z B u v c d) (lipschitz R E T c d*A) D := by
  have hz := h.andE₁.andE₁
  have ha := h.andE₂.andE₁
  have hu := h.andE₂.andE₂.andE₁
  have hD := h.andE₂.andE₂.andE₂.andE₁
  have hd := h.andE₁.andE₂.andE₂
  have raw := GaussianNamedMultiplyRate.independent_rate powerF decayF powerF decayF
    (powerData z B a b) (decayData (c*a) (d*b)) (powerData z B u v) (decayData (c*u) (d*v))
    (GaussianEulerCompactPowerVariation.lipschitz R E T*A) D (decayLipschitz T c*A) D
    (decayBound T c) (GaussianEulerCompactPowerMajorant.majorant R E T) hD hD
    (GaussianEulerIntegrandName.power_regular z B a b (.andI hz.andE₁ ha.andE₁)) (GaussianEulerPositiveScalingIntegrand.decay_regular _ _)
    (GaussianEulerIntegrandName.power_regular z B u v (.andI hz.andE₁ hu.andE₁)) (GaussianEulerPositiveScalingIntegrand.decay_regular _ _)
    (decay_sample_bound T c d a b E hd ha) (power_sample_bound z R B E T u v hz hu)
    (GaussianEulerCompactPowerVariation.original_power_rate z R B E T a b u v A D (.andI hz h.andE₂))
    (original_decay_rate T c d a b u v E A D hd ha hu hD h.andE₂.andE₂.andE₂.andE₂)
  have reduced : Γ ⊢[PRAAx] independentRate dampedF dampedF (dampedData z B a b c d) (dampedData z B u v c d)
      ((lipschitz R E T c d*A)*D) (D*D) :=
    GaussianEulerCompactModulus.rate_congr _ _ _ _ _ _ _
      (by unfold GaussianNamedMultiplyRate.leadingNumerator lipschitz; ipra_ring) raw
  exact cancel_rate_denominator _ _ _ _ _ _ hD reduced

theorem actual_original_damped_Euler_compact_time_rate_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
    (input (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
      independentRate dampedF dampedF (dampedData (var 0) (var 2) (var 7) (var 8) (var 5) (var 6))
        (dampedData (var 0) (var 2) (var 9) (var 10) (var 5) (var 6))
        (lipschitz (var 1) (var 3) (var 4) (var 5) (var 6)*var 11) (var 12)) :=
  closeUniv 13 (.impI (original_rate _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerDampedTimeRate
