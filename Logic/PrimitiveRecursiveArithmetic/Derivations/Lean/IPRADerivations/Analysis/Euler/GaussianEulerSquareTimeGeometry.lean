import IPRADerivations.Analysis.Integration.GaussianRationalQuadratureSquareJacobian
import IPRADerivations.Analysis.Euler.GaussianEulerDampedTimeRate
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactModulus

/-!
# Compact geometry and actual Euler bounds for quadratic time

Positive times in [1/E,T] map under (c/d)u^2 into
[1/(d*E^2),c*T^2]. The original fraction distance grows by at most
2*c*T, and the actual Jacobian grows by at most 2*c. The bound on the
unchanged Euler observations is proved from their actual finite scalar
sums, including their independently computed exponent clocks/radii.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerSquareTimeGeometry

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCompactLogarithmBounds (domain)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalQuadratureSquareCells (jacobian)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def lowerDenominator (d E : PTm n) : PTm n := d*E*E
def upperEndpoint (c T : PTm n) : PTm n := c*T*T
def majorant (R E T c d : PTm n) : PTm n := pw (num 3)
  (GaussianEulerExponentCompactBounds.radius R (lowerDenominator d E) (upperEndpoint c T))
def source (z R B E c d : PTm n) : Fm PTm n := GaussianEulerExponentCompactBounds.source z R B E ⋏ (le one c ⋏ le one d)

@[simp] theorem subst_lowerDenominator {m : ℕ} (σ : Fin n → PTm m) (d E : PTm n) :
    Syn.subst σ (lowerDenominator d E) = lowerDenominator (Syn.subst σ d) (Syn.subst σ E) := by simp [lowerDenominator]
@[simp] theorem subst_upperEndpoint {m : ℕ} (σ : Fin n → PTm m) (c T : PTm n) :
    Syn.subst σ (upperEndpoint c T) = upperEndpoint (Syn.subst σ c) (Syn.subst σ T) := by simp [upperEndpoint]
@[simp] theorem subst_majorant {m : ℕ} (σ : Fin n → PTm m) (R E T c d : PTm n) :
    Syn.subst σ (majorant R E T c d) = majorant (Syn.subst σ R) (Syn.subst σ E) (Syn.subst σ T) (Syn.subst σ c) (Syn.subst σ d) := by simp [majorant]
@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (z R B E c d : PTm n) :
    (source z R B E c d).subst σ = source (Syn.subst σ z) (Syn.subst σ R) (Syn.subst σ B)
      (Syn.subst σ E) (Syn.subst σ c) (Syn.subst σ d) := by simp [source]

theorem mapped_source (z R B E c d : PTm n) (h : Γ ⊢[PRAAx] source z R B E c d) : Γ ⊢[PRAAx]
    GaussianEulerExponentCompactBounds.source z R B (lowerDenominator d E) :=
  .andI h.andE₁.andE₁ (.andI (positive_product _ _ (positive_product _ _ h.andE₂.andE₂ h.andE₁.andE₂.andE₁) h.andE₁.andE₂.andE₁) h.andE₁.andE₂.andE₂)

theorem mapped_domain (a b E T c d : PTm n) (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    domain (c*a*a) (d*b*b) (lowerDenominator d E) (upperEndpoint c T) := by
  have low := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono h.andE₂.andE₁ h.andE₂.andE₁
  have up := LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono h.andE₂.andE₂ h.andE₂.andE₂
  have lower₁ : Γ ⊢[PRAAx] le (d*b*b) (d*E*E*a*a) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right d low)
  have lower₂ : Γ ⊢[PRAAx] le (d*E*E*a*a) ((d*E*E)*(c*a*a)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (d*E*E*a*a) hc)
  have upper₁ : Γ ⊢[PRAAx] le (c*a*a) (c*T*T*b*b) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right c up)
  have upper₂ : Γ ⊢[PRAAx] le (c*T*T*b*b) ((c*T*T)*(d*b*b)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (c*T*T*b*b) hd)
  exact .andI (.andI (positive_product _ _ (positive_product _ _ hc h.andE₁.andE₁) h.andE₁.andE₁)
    (positive_product _ _ (positive_product _ _ hd h.andE₁.andE₂) h.andE₁.andE₂)) (.andI (le_trans lower₁ lower₂) (le_trans upper₁ upper₂))

theorem mapped_distance (a b u v E T c d A D : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (ha : Γ ⊢[PRAAx] domain a b E T) (hu : Γ ⊢[PRAAx] domain u v E T) (hD : Γ ⊢[PRAAx] le one D)
    (near : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction u v) A D) : Γ ⊢[PRAAx]
    distanceBounded (fraction (c*a*a) (d*b*b)) (fraction (c*u*u) (d*v*v)) (two*c*T*A) D := by
  have ba := GaussianEulerExponentCompactBounds.fraction_bound a b T ha.andE₁.andE₂ ha.andE₂.andE₂
  have bu := GaussianEulerExponentCompactBounds.fraction_bound u v T hu.andE₁.andE₂ hu.andE₂.andE₂
  have raw : Γ ⊢[PRAAx] distanceBounded (qmul (fraction a b) (fraction a b)) (qmul (fraction u v) (fraction u v)) (A*T+T*A) D :=
    GaussianNameArithmetic.product_distance (fraction a b) (fraction u v) (fraction a b) (fraction u v)
      A A D T T hD near near ba bu
  have squares : Γ ⊢[PRAAx] distanceBounded (fraction (a*a) (b*b)) (fraction (u*u) (v*v)) (two*T*A) D :=
    distance_congr (GaussianEulerDampedTimeRate.fraction_product a b a b ha.andE₁.andE₂ ha.andE₁.andE₂)
      (GaussianEulerDampedTimeRate.fraction_product u v u v hu.andE₁.andE₂ hu.andE₁.andE₂) (by ipra_ring) (.eqRefl _) raw
  have scaled := GaussianEulerDampedTimeRate.scaled_time_distance c d (a*a) (b*b) (u*u) (v*v) (two*T*A) D hd
    (positive_product _ _ ha.andE₁.andE₂ ha.andE₁.andE₂) (positive_product _ _ hu.andE₁.andE₂ hu.andE₁.andE₂) hD squares
  exact distance_congr (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring))
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)) (by ipra_ring) (.eqRefl _) scaled

theorem jacobian_distance (a b u v c d A D : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (hb : Γ ⊢[PRAAx] le one b) (hv : Γ ⊢[PRAAx] le one v) (hD : Γ ⊢[PRAAx] le one D)
    (near : Γ ⊢[PRAAx] distanceBounded (fraction a b) (fraction u v) A D) : Γ ⊢[PRAAx]
    distanceBounded (jacobian c d (pairT a b)) (jacobian c d (pairT u v)) (two*c*A) D :=
  distance_congr (GaussianCompactRiemannName.fraction_congr _ _ _ _
    (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm)
    (GaussianCompactRiemannName.fraction_congr _ _ _ _
      (congrMul (.eqRefl _) (fst_pair _ _)).eqSymm (congrMul (.eqRefl _) (snd_pair _ _)).eqSymm) (.eqRefl _) (.eqRefl _)
    (GaussianEulerDampedTimeRate.scaled_time_distance (two*c) d a b u v A D hd hb hv hD near)

theorem jacobian_bound (a b E T c d : PTm n) (hd : Γ ⊢[PRAAx] le one d)
    (h : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx] bounded (jacobian c d (pairT a b)) (two*c*T) one := by
  have upper₁ : Γ ⊢[PRAAx] le (two*c*a) (two*c*T*b) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*c) h.andE₂.andE₂)
  have upper₂ : Γ ⊢[PRAAx] le (two*c*T*b) ((two*c*T)*(d*b)) :=
    le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (two*c*T*b) hd)
  exact GaussianRationalReciprocal.bound_congr
    (GaussianCompactRiemannName.fraction_congr _ _ _ _ (congrMul (.eqRefl _) (fst_pair _ _))
      (congrMul (.eqRefl _) (snd_pair _ _))).eqSymm (.eqRefl _) (.eqRefl _)
    (GaussianEulerExponentCompactBounds.fraction_bound _ _ _ (positive_product _ _ hd h.andE₁.andE₂) (le_trans upper₁ upper₂))

theorem original_mapped_observation_bound (p z R B E T c d a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E c d) (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (GaussianEulerIntegrandName.sample p z B (c*a*a) (d*b*b)) (majorant R E T c d) one := by
  let X := GaussianEulerIntegrandName.exponentData z B (c*a*a) (d*b*b)
  let R₀ := GaussianEulerIntegrandName.radius z B (c*a*a) (d*b*b)
  let M := GaussianEulerExponentCompactBounds.radius R (lowerDenominator d E) (upperEndpoint c T)
  have ht' := mapped_domain a b E T c d h.andE₂.andE₁ h.andE₂.andE₂ ht
  have point := GaussianEulerExponentCompactBounds.exponent_bound (GaussianRadiusExponentialName.inputPrecision R₀ p)
    z R B (lowerDenominator d E) (upperEndpoint c T) (c*a*a) (d*b*b) (mapped_source z R B E c d h) ht'
  have finite := GaussianPositiveExponentialMajorant.disk_bound _ M (GaussianRadiusExponentialName.index R₀ p) point
  have readback : Γ ⊢[PRAAx] GaussianEulerIntegrandName.sample p z B (c*a*a) (d*b*b) ≐
      GaussianRadiusExponentialName.value GaussianEulerIntegrandName.exponentF R₀ p X :=
    (GaussianEulerIntegrandName.sample_at p z B _ _).eqTrans
      (GaussianRadiusExponentialName.sample_at GaussianEulerIntegrandName.exponentF R₀ p X)
  exact GaussianRationalReciprocal.bound_congr readback.eqSymm (.eqRefl _) (.eqRefl _) finite

theorem actual_jacobian_observation_bound (p z R B E T c d a b : PTm n)
    (h : Γ ⊢[PRAAx] source z R B E c d) (ht : Γ ⊢[PRAAx] domain a b E T) : Γ ⊢[PRAAx]
    bounded (ap3 (GaussianRationalQuadratureSquareJacobian.jacobianF GaussianEulerIntegrandName.evaluatorF) p (pairT a b)
      (GaussianRationalQuadratureDilation.pullData c d (GaussianEulerIntegrandName.fixedData z B)))
      ((two*c*T)*majorant R E T c d) one := by
  have time : Γ ⊢[PRAAx] GaussianRationalQuadratureSquareCells.timeMap c d (pairT a b) ≐ pairT (c*a*a) (d*b*b) :=
    congrPairT (congrMul (congrMul (.eqRefl _) (fst_pair _ _)) (fst_pair _ _))
      (congrMul (congrMul (.eqRefl _) (snd_pair _ _)) (snd_pair _ _))
  have mapped : Γ ⊢[PRAAx] bounded (ap3 GaussianEulerIntegrandName.evaluatorF p
      (GaussianRationalQuadratureSquareCells.timeMap c d (pairT a b)) (GaussianEulerIntegrandName.fixedData z B))
      (majorant R E T c d) one :=
    GaussianRationalReciprocal.bound_congr (congrAp3 _ (.eqRefl _) time (.eqRefl _)).eqSymm (.eqRefl _) (.eqRefl _)
      (original_mapped_observation_bound p z R B E T c d a b h ht)
  have product := GaussianRationalReciprocal.bounded_product _ _ _ _ _ _ (le_refl one) (le_refl one)
    (jacobian_bound a b E T c d h.andE₂.andE₂ ht) mapped
  exact GaussianRationalReciprocal.bound_congr
    (GaussianRationalQuadratureSquareJacobian.jacobian_at GaussianEulerIntegrandName.evaluatorF p (pairT a b) c d
      (GaussianEulerIntegrandName.fixedData z B)).eqSymm (.eqRefl _) (by ipra_ring) product

theorem actual_original_square_time_Euler_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 1) (var 2) (var 3) (var 4) (var 6) (var 7) ⟶ domain (var 8) (var 9) (var 4) (var 5) ⟶
      bounded (GaussianEulerIntegrandName.sample (var 0) (var 1) (var 3) (var 6*var 8*var 8) (var 7*var 9*var 9))
        (majorant (var 2) (var 4) (var 5) (var 6) (var 7)) one) :=
  closeUniv 10 (.impI (.impI (original_mapped_observation_bound _ _ _ _ _ _ _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerSquareTimeGeometry
