import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayAddition

/-!
# First-order increments of the original Euler decay

At the original rational observations, the value at t+h differs from
the first-order step E(t)(1-h) by at most 3h²+20·2⁻ᵖ. The bound is
uniform in the positive starting time. It supports direct finite
telescoping on quadrature meshes.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayIncrement

open_ipra
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianEulerDecayAddition (original_decay_add original_decay_linear_remainder)
open GaussianEulerDecayFactorBounds (original_half_decay_factor_bound)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianNameArithmetic (multiplyF multiplyData multiplyModulus multiply_at)
open GaussianNameEquivalence (point_at cross_diagonal_at)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianRationalHorner (canonical positive_product qadd qmul qmul_canonical)
open GaussianRationalSyntheticDivision (qmul_congr qone)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same distance_symmetric)
open GaussianRationalReciprocal (bound_congr power power_zero)
open GaussianEuclideanDistanceName (pointCN)
open GaussianNameRingLaws (three)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private abbrev value (a b p : PTm n) : PTm n := ap2 decayF p (decayData a b)

private theorem decay_regular (a b : PTm n) : Γ ⊢[PRAAx] pointCN decayF (decayData a b) :=
  GaussianRadiusExponentialName.name_regular constantF _ _ (GaussianGammaFiniteApproximantName.exponential_input
    constantF (decayPoint a b) (constant_regular _))

theorem decay_observation_uniform_bound (a b p : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] bounded (value a b p) three one := by
  let P := unit p
  let X := value a b p
  let Q := GaussianDominantPairAlgebra.radiusPoint (two*a) b
  have hX : Γ ⊢[PRAAx] canonical X := GaussianRadiusExponentialName.sample_canonical constantF _ p (decayPoint a b)
  have e : Γ ⊢[PRAAx] qmul (power Q zero) X ≐ X :=
    (qmul_congr (power_zero Q) (.eqRefl _)).eqTrans
      ((GaussianRationalPowerAlgebra.qmul_commutative qone X).eqTrans (GaussianReciprocalHorner.qmul_one_right X hX))
  have numerator : Γ ⊢[PRAAx] unit zero*Products.fact zero*P+two*pw (two*a) zero ≐ P+two := by
    have a0 : Γ ⊢[PRAAx] unit zero ≐ one := pw_zero two
    have b0 : Γ ⊢[PRAAx] Products.fact zero ≐ one := ExponentialSeries.fact_zero'
    have c0 : Γ ⊢[PRAAx] pw (two*a) zero ≐ one := pw_zero _
    exact (congrAdd (congrMul (congrMul a0 b0) (.eqRefl P)) (congrMul (.eqRefl two) c0)).eqTrans (by ipra_ring)
  have bound := bound_congr e numerator (.eqRefl _) (original_half_decay_factor_bound a b zero p ha hb)
  apply bounded_radius_mono _ (P+two) P three one (unit_positive p) (le_refl one) _ bound
  have grow : Γ ⊢[PRAAx] le (P+one*two) (P+P*two) :=
    add_le_add₂ (le_refl P) (mul_le_mul_right two (unit_positive p))
  exact le_congr (by dsimp only [P]; ipra_ring) (by dsimp only [P,three]; ipra_ring)
    grow

private theorem decay_precision_mono (a b p k : PTm n) (hp : Γ ⊢[PRAAx] le p k) :
    Γ ⊢[PRAAx] distanceBounded (value a b k) (value a b p) two (unit p) := by
  have U := GaussianExponentialReference.unit_monotone hp
  refine distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive k) (unit_positive p))
    (unit_positive p) ?_ (point_at decayF (decayData a b) k p (decay_regular a b))
  exact le_congr (by ipra_ring) (by ipra_ring)
    (add_le_add₂ (le_refl (unit k*unit p)) (mul_le_mul_right (unit p) U))

theorem decay_product_observation (a b c d p : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] distanceBounded (value (a*d+c*b) (b*d) p) (qmul (value a b p) (value c d p))
      (num 14) (unit p) := by
  let x := decayData a b
  let y := decayData c d
  let X := ap2 (multiplyF decayF decayF) p (multiplyData decayF decayF x y)
  let K := GaussianFastValueCut.exponent (multiplyModulus decayF decayF x y) p
  have hK : Γ ⊢[PRAAx] le p K := le_add_right _ _
  have read : Γ ⊢[PRAAx] X ≐ qmul (value a b K) (value c d K) :=
    (multiply_at decayF decayF x y p).eqTrans
      (GaussianExponentialReference.recode_fixed _ (qmul_canonical _ _))
  have blend := GaussianNameArithmetic.product_distance (value a b K) (value a b p) (value c d K) (value c d p)
    two two (unit p) three three (unit_positive p)
    (decay_precision_mono a b p K hK) (decay_precision_mono c d p K hK)
    (decay_observation_uniform_bound c d K hc hd) (decay_observation_uniform_bound a b p ha hb)
  have known := cross_diagonal_at p (original_decay_add a b c d hb hd)
  have first := distance_symmetric _ _ _ _ (unit_positive p) known
  have second := distance_congr read.eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) blend
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [three]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive p) first second)

theorem decay_linear_increment (a b c d p : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hc : Γ ⊢[PRAAx] le one c) (hd : Γ ⊢[PRAAx] le one d) (hcd : Γ ⊢[PRAAx] le c d) :
    Γ ⊢[PRAAx] distanceBounded (value (a*d+c*b) (b*d) p)
      (qmul (value a b p) (qadd qone (decayPoint c d)))
      (three*c*c*unit p+num 20*(d*d)) (d*d*unit p) := by
  let D := d*d*unit p
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (positive_product d d hd hd) (unit_positive p)
  have error := original_decay_linear_remainder c d p hd hcd
  have step := GaussianApproximateInverseDistance.multiply_distance (value a b p) (value c d p)
    (qadd qone (decayPoint c d)) three (c*c*unit p+two*(d*d)) D hD
    (decay_observation_uniform_bound a b p ha hb) error
  have grows : Γ ⊢[PRAAx] le (num 14*D) (num 14*(d*d)*unit p) :=
    le_congr (by dsimp only [D]; ipra_ring) (.eqRefl _) (le_refl (num 14*(d*d)*unit p))
  have product := distance_radius_mono _ _ (num 14) (unit p) (num 14*(d*d)) D (unit_positive p) hD grows
    (decay_product_observation a b c d p ha hb hc hd)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [three]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hD product step)

theorem original_Euler_decay_linear_increment_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    ((le one (var 0) ⋏ le one (var 1)) ⟶ (le one (var 2) ⋏ le one (var 3)) ⟶ le (var 2) (var 3) ⟶
      distanceBounded (value (var 0*var 3+var 2*var 1) (var 1*var 3) (var 4))
        (qmul (value (var 0) (var 1) (var 4)) (qadd qone (decayPoint (var 2) (var 3))))
        (three*var 2*var 2*unit (var 4)+num 20*(var 3*var 3)) (var 3*var 3*unit (var 4))) :=
  closeUniv 5 (.impI (.impI (.impI (decay_linear_increment _ _ _ _ _
    hyp2.andE₁ hyp2.andE₂ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayIncrement
