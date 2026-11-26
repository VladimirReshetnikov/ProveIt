import IPRADerivations.Analysis.Euler.PositiveAxis.UnitTime.GaussianEulerUnitNormalizationIntegrand
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayCompactAntiderivative
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Exponential.Names.GaussianExponentialSmallPerturbation
import IPRADerivations.Analysis.Gamma.Integrals.GaussianGammaEulerCompactQuadrature

/-!
# Original unit-input Euler compact observations and the decay endpoints

The literal equality of the original evaluators transports the checked
finite antiderivative. Endpoint estimates use only the original finite
small exponential and the original positive integer decay bound.
No Gamma normalization theorem enters this finite integral calculation.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitNormalizationCompact

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode)
open GaussianEulerIntegrandName (evaluatorF fixedData decayF decayData decayPoint)
open GaussianEulerDecayQuadraturePrecision (endpointDifference)
open GaussianEulerDecayCompactAntiderivative (endpointF endpointData endpoint_at)
open GaussianCompactRiemannName (quadrature nameF data)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalSyntheticDivision (qone)
open GaussianRationalHorner (positive_product)
open GaussianCoefficientNameBounds (unit unit_positive)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem original_compact_is_decay (p a C E L T x : PTm n) : Γ ⊢[PRAAx]
    ap2 (nameF evaluatorF) p (data a C E L T (fixedData oneCode one)) ≐
      ap2 (nameF GaussianEulerDecayQuadrature.evaluatorF) p (data a C E L T x) :=
  (GaussianCompactRiemannName.name_at evaluatorF p a C E L T _).eqTrans
    ((GaussianEulerUnitNormalizationIntegrand.original_grid_is_decay _ _ _ _ _ x).eqTrans
      (GaussianCompactRiemannName.name_at GaussianEulerDecayQuadrature.evaluatorF p a C E L T x).eqSymm)

theorem original_compact_endpoint (p q a C E L T x : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hC : Γ ⊢[PRAAx] le one C) (hE : Γ ⊢[PRAAx] le one E)
    (hL : Γ ⊢[PRAAx] le one L) (hwidth : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    distanceBounded (ap2 (nameF evaluatorF) p (data a C E L T (fixedData oneCode one)))
      (endpointDifference a C E (q+one)) (unit p+unit q) (unit p*unit q) :=
  distance_congr (original_compact_is_decay p a C E L T x).eqSymm (endpoint_at q a C E)
    (.eqRefl _) (.eqRefl _) (GaussianEulerDecayCompactAntiderivative.compact_observations p q a C E L T x
      ha hC hE hL hwidth (GaussianEulerDecayCompactAntiderivative.mesh_covers_step p C E L T hwidth hL))

theorem original_decay_finite_sum (p a b : PTm n) : Γ ⊢[PRAAx]
    ap2 decayF p (decayData a b) ≐ GaussianRationalPolynomialExponential.scalarSum (decayPoint a b)
      (GaussianRadiusExponentialName.index (GaussianNameBounds.U GaussianGammaCanonicalExponent.constantF (decayPoint a b)) p) :=
  (GaussianRadiusExponentialName.sample_at GaussianGammaCanonicalExponent.constantF _ p (decayPoint a b)).eqTrans
    (GaussianRationalFiniteSum.sum_index_congr GaussianRationalPolynomialExponential.scalarBody (.eqRefl _)
      (GaussianGammaCanonicalExponent.constant_at _ _))

theorem original_left_endpoint_near_one (p E : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    distanceBounded (ap2 decayF p (decayData one E)) qone (LeanProofs.IPRA.PTm.num 3) E := by
  have fraction := GaussianRationalReciprocal.bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one E hE).eqSymm
    (.eqRefl _) (.eqRefl _) (GaussianDominantPairAlgebra.radius_bounded one E hE)
  have neg := GaussianRationalReciprocal.bounded_negative _ one E hE fraction
  exact distance_congr (original_decay_finite_sum p one E).eqSymm (.eqRefl _)
    (by ipra_ring) (.eqRefl _) (GaussianExponentialSmallPerturbation.finite_perturbation _ one E _ hE hE neg)

theorem original_endpoint_difference_near_one (p E T : PTm n) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    distanceBounded (qsub (ap2 decayF p (decayData one E)) (ap2 decayF p (decayData T one))) qone
      (LeanProofs.IPRA.PTm.num 3*unit T*unit p+E*(unit p+two*unit T)) (E*(unit T*unit p)) := by
  have hp := unit_positive (Γ := Γ) p
  have ht := unit_positive (Γ := Γ) T
  have den := positive_product _ _ ht hp
  have full := positive_product _ _ hE den
  have first : Γ ⊢[PRAAx] distanceBounded (ap2 decayF p (decayData one E)) qone
      (LeanProofs.IPRA.PTm.num 3*(unit T*unit p)) (E*(unit T*unit p)) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ hE full
      (le_of_eq_add (d := zero) (by ipra_ring)) (original_left_endpoint_near_one p E hE)
  have minus := GaussianRationalReciprocal.bounded_negative (ap2 decayF p (decayData T one))
    (unit p+two*unit T) (unit T*unit p) den (GaussianEulerDecayFactorBounds.original_integer_decay_bound T p)
  have near := (GaussianReconstructionRoots.distance_zero_iff _ _ _ den).iffMpr minus
  have second : Γ ⊢[PRAAx] distanceBounded (GaussianRationalMetric.qnegative (ap2 decayF p (decayData T one))) GaussianRationalHorner.qzero
      (E*(unit p+two*unit T)) (E*(unit T*unit p)) :=
    GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ _ _ den full
      (le_of_eq_add (d := zero) (by ipra_ring)) near
  have raw := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ full first second
  exact distance_congr (.eqRefl _)
    (GaussianReciprocalHorner.qadd_zero_right qone GaussianRationalSyntheticDivision.qone_canonical)
    (by ipra_ring) (.eqRefl _) raw

theorem original_unit_Euler_compact_antiderivative_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    ((le one (var 2) ⋏ (le one (var 3) ⋏ (le one (var 4) ⋏ (le one (var 5) ⋏ le (var 3) (var 4*var 6))))) ⟶
      distanceBounded (ap2 (nameF evaluatorF) (var 0) (data (var 2) (var 3) (var 4) (var 5) (var 6) (fixedData oneCode one)))
        (endpointDifference (var 2) (var 3) (var 4) (var 1+one)) (unit (var 0)+unit (var 1)) (unit (var 0)*unit (var 1))) :=
  closeUniv 8 (.impI (original_compact_endpoint _ _ _ _ _ _ _ (var 7) Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitNormalizationCompact
