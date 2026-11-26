import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactExhaustionScaled
import IPRADerivations.Analysis.Euler.GaussianEulerDampedTimeRate

/-!
# Removal of the exact chart coefficient from cofinal observations

The target name is the original inverse-scale/Gamma product multiplied
by the exact rational f/e. Its bounded product clock pays for the target
observation error. Exact reciprocal cancellation then converts a bound
for (e/f)*X into one for the original canonical sample X.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionNormalization

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerCompactExhaustionScaled (referenceF referenceData reference_regular)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (qmul canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

abbrev nameF : PR 2 := GaussianBoundedConstantProductName.nameF referenceF
def data (z R B A e f d h L Q : PTm n) : PTm n :=
  GaussianBoundedConstantProductName.data L (fraction f e) (referenceData z R B A e f d h L Q)
def referenceClock (p L : PTm n) : PTm n := GaussianBoundedConstantProductName.clock p L
def approximation (s q x z R B A e f d h L Q : PTm n) : Fm PTm n :=
  let p := referenceClock q L
  distanceBounded (qmul (fraction e f) x) (ap2 referenceF p (referenceData z R B A e f d h L Q))
    (unit s+unit p) (unit s*unit p)

theorem exact_inverse_product (e f : PTm n) (he : Γ ⊢[PRAAx] le one e)
    (hf : Γ ⊢[PRAAx] le one f) : Γ ⊢[PRAAx] qmul (fraction f e) (fraction e f) ≐ qone := by
  have hfe := positive_product _ _ hf he
  have raw := GaussianEulerDampedTimeRate.fraction_product f e e f he hf
  have mid : Γ ⊢[PRAAx] fraction (f*e) (e*f) ≐ fraction ((f*e)*one) ((f*e)*one) :=
    GaussianCompactRiemannName.fraction_congr _ _ _ _ (by ipra_ring) (by ipra_ring)
  exact raw.eqTrans (mid.eqTrans
    ((GaussianCompactRiemannSplit.fraction_cancel (f*e) one one hfe (le_refl one)).eqTrans
      GaussianGammaFactorialValues.natural_one))

theorem exact_cancel (e f x : PTm n) (he : Γ ⊢[PRAAx] le one e)
    (hf : Γ ⊢[PRAAx] le one f) (hx : Γ ⊢[PRAAx] canonical x) :
    Γ ⊢[PRAAx] qmul (fraction f e) (qmul (fraction e f) x) ≐ x :=
  (GaussianReciprocalHorner.qmul_associative (fraction f e) (fraction e f) x).eqSymm.eqTrans
    ((qmul_congr (exact_inverse_product e f he hf) (.eqRefl x)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative qone x).eqTrans
        (GaussianReciprocalHorner.qmul_one_right x hx)))

theorem inverse_bound (e f L : PTm n) (he : Γ ⊢[PRAAx] le one e)
    (hle : Γ ⊢[PRAAx] le f (L*e)) : Γ ⊢[PRAAx] bounded (fraction f e) L one :=
  GaussianEulerExponentCompactBounds.fraction_bound f e L he hle

theorem name_regular (z R B A e f d h L Q : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPowerScalingParameter.source z R B A e f L Q)
    (hd : Γ ⊢[PRAAx] GaussianPositiveRationalLogarithm.source d h) :
    Γ ⊢[PRAAx] pointCN nameF (data z R B A e f d h L Q) :=
  GaussianBoundedConstantProductName.name_regular referenceF L (fraction f e) _
    (.andI (reference_regular z R B A e f d h L Q hs hd)
      (inverse_bound e f L hs.andE₂.andE₁ hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁))

theorem remove_chart_coefficient (s q x z R B A e f d h L Q : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPowerScalingParameter.source z R B A e f L Q)
    (hx : Γ ⊢[PRAAx] canonical x)
    (ha : Γ ⊢[PRAAx] approximation s q x z R B A e f d h L Q) :
    Γ ⊢[PRAAx] distanceBounded x (ap2 nameF q (data z R B A e f d h L Q))
      (L*unit q+unit s) (unit s*unit q) := by
  let p := referenceClock q L
  let y := referenceData z R B A e f d h L Q
  have he := hs.andE₂.andE₁
  have hf := hs.andE₂.andE₂.andE₁
  have hb := inverse_bound e f L he hs.andE₂.andE₂.andE₂.andE₂.andE₂.andE₁
  have hDen := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive p)
  have mul := GaussianApproximateInverseDistance.multiply_distance (fraction f e) (qmul (fraction e f) x)
    (ap2 referenceF p y) L _ _ hDen hb ha
  have exactSample := GaussianBoundedConstantProductName.sample_at (Γ := Γ) referenceF q L (fraction f e) y
  have budget : Γ ⊢[PRAAx] le (L*unit q) (unit p) :=
    GaussianFastValueCut.query_budget L q
  have bound : Γ ⊢[PRAAx] le ((L*(unit s+unit p))*(unit s*unit q)) ((L*unit q+unit s)*(unit s*unit p)) := by
    ipra_le (𝔞(unit s))^2*sl budget
  exact distance_radius_mono _ _ _ _ _ _ hDen (positive_product _ _ (unit_positive _) (unit_positive _)) bound
    (distance_congr (exact_cancel e f x he hf hx) exactSample.eqSymm (.eqRefl _) (.eqRefl _) mul)

theorem paid_clock (p L : PTm n) : Γ ⊢[PRAAx] le (L*unit p) (unit (referenceClock p L)) :=
  GaussianFastValueCut.query_budget L p

theorem remove_chart_coefficient_at_paid_clock (p s q x z R B A e f d h L Q : PTm n)
    (hs : Γ ⊢[PRAAx] GaussianEulerPowerScalingParameter.source z R B A e f L Q)
    (hx : Γ ⊢[PRAAx] canonical x)
    (hp : Γ ⊢[PRAAx] le (L*unit p) (unit s))
    (ha : Γ ⊢[PRAAx] approximation s q x z R B A e f d h L Q) :
    Γ ⊢[PRAAx] distanceBounded x (ap2 nameF q (data z R B A e f d h L Q))
      (unit p+unit q) (unit p*unit q) := by
  have bound : Γ ⊢[PRAAx]
      le ((L*unit q+unit s)*(unit p*unit q)) ((unit p+unit q)*(unit s*unit q)) := by
    ipra_le (𝔞(unit q))^2*sl hp
  exact distance_radius_mono _ _ _ _ _ _
    (positive_product _ _ (unit_positive _) (unit_positive _))
    (positive_product _ _ (unit_positive _) (unit_positive _)) bound
    (remove_chart_coefficient s q x z R B A e f d h L Q hs hx ha)

theorem actual_original_cofinal_observation_remove_chart_coefficient_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      ((GaussianEulerPowerScalingParameter.source (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 11) (var 12) ⋏
        canonical (var 2)) ⟶
        approximation (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12) ⟶
        distanceBounded (var 2) (ap2 nameF (var 1)
          (data (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) (var 12)))
          (var 11*unit (var 1)+unit (var 0)) (unit (var 0)*unit (var 1))) :=
  closeUniv 13 (.impI (.impI (remove_chart_coefficient _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerCompactExhaustionNormalization
