import IPRADerivations.Analysis.Euler.Integration.Parts.CompactNames.GaussianEulerIntegrationByPartsCompactNames
import IPRADerivations.Analysis.Integration.CompactGrids.GaussianCompactMeshIndependence

/-!
# Literal readbacks of the regular compact IBP programs

The unchanged normalized left and boundary names are compared with the
same-query original compact values and endpoint observations. Any actual
positive refinement of the original compact mesh keeps its proved
readback budget. The endpoint comparison permits independent later
queries without equating their original evaluator clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCompactNameObservations

open_ipra
open GaussianEulerCompactAdditivity (intervalSource)
open GaussianEulerIntegrationByPartsCompactNames
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianRationalHorner (ofGaussian qmul positive_product)
open GaussianRationalMetric (distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (point_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rawLeft (t z R B a C E T : PTm n) : PTm n := qsub
  (qmul (ofGaussian z B) (ap2 compactF t (compactData z R B a C E T)))
  (ap2 compactF t (compactData (GaussianGammaEulerHeadShift.shifted z B) R B a C E T))

ipra_subst rawLeft

theorem left_readback (t z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 leftF t (leftData z R B a C E T)) (rawLeft t z R B a C E T)
      (productModulus z R B a C E T+num 7) (unit t) := by
  have names := compact_regular z R B a C E T h
  have first := GaussianNamedDifference.sample_error productF compactF _ _ t (product_regular z R B a C E T h) names.andE₂
  have raw := GaussianNameRingLaws.multiply_sample_error constantF compactF (ofGaussian z B) (compactData z R B a C E T) t (constant_regular _) names.andE₁
  have product := distance_congr (.eqRefl _)
    (GaussianRationalSyntheticDivision.qmul_congr (constant_at t (ofGaussian z B)) (.eqRefl _)) (.eqRefl _) (.eqRefl _) raw
  have same := GaussianRationalPowerDifference.distance_refl_zero (Γ := Γ)
    (ap2 compactF t (compactData (GaussianGammaEulerHeadShift.shifted z B) R B a C E T)) (unit t) (unit_positive t)
  have second := GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ (unit_positive t) product same
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [productModulus]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (unit_positive t) first second)

theorem boundary_readback (t z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) : Γ ⊢[PRAAx]
    distanceBounded (ap2 boundaryF t (boundaryData z B a C E))
      (GaussianEulerIntegrationByPartsCompact.boundary t z B a C E) (num 6) (unit t) := by
  have names := endpoint_regular z R B a C E T h
  exact distance_congr (.eqRefl _)
    (GaussianRationalSyntheticDivision.qsub_congr (GaussianEulerIntegrandName.sample_at t _ _ _ _).eqSymm
      (GaussianEulerIntegrandName.sample_at t _ _ _ _).eqSymm) (.eqRefl _) (.eqRefl _)
    (GaussianNamedDifference.sample_error _ _ _ _ t names.andE₁ names.andE₂)

theorem endpoint_query_error (p t z B a E : PTm n)
    (h : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN GaussianEulerIntegrandName.nameF (GaussianEulerIntegrandName.data z B a E))
    (hp : Γ ⊢[PRAAx] le t p) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerIntegrandName.sample p z B a E) (GaussianEulerIntegrandName.sample t z B a E) two (unit t) := by
  have near := point_at GaussianEulerIntegrandName.nameF (GaussianEulerIntegrandName.data z B a E) p t h
  have grow := GaussianExponentialReference.unit_monotone (Γ := Γ) hp
  have hd := positive_product (Γ := Γ) _ _ (unit_positive p) (unit_positive t)
  have reduced := distance_radius_mono _ _ _ _ two (unit t) hd (unit_positive t)
    (le_congr (by ipra_ring) (by ipra_ring) (add_le_add₂ (le_refl (unit p*unit t)) (mul_le_mul_right (unit t) grow))) near
  exact distance_congr (GaussianEulerIntegrandName.sample_at p _ _ _ _).eqSymm
    (GaussianEulerIntegrandName.sample_at t _ _ _ _).eqSymm (.eqRefl _) (.eqRefl _) reduced

theorem boundary_query_error (p t z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hp : Γ ⊢[PRAAx] le t p) : Γ ⊢[PRAAx]
    distanceBounded (GaussianEulerIntegrationByPartsCompact.boundary p z B a C E)
      (GaussianEulerIntegrationByPartsCompact.boundary t z B a C E) (num 4) (unit t) := by
  have names := endpoint_regular z R B a C E T h
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (GaussianNamedDifference.difference_distance _ _ _ _ _ _ _ (unit_positive t)
      (endpoint_query_error p t _ _ _ _ names.andE₁ hp) (endpoint_query_error p t _ _ _ _ names.andE₂ hp))

theorem grid_to_compact (t p H z R B a C E T : PTm n)
    (h : Γ ⊢[PRAAx] intervalSource z R B a C E T) (hH : Γ ⊢[PRAAx] le one H)
    (hp : Γ ⊢[PRAAx] le (GaussianCompactRiemannName.precision t T) p) : Γ ⊢[PRAAx]
    distanceBounded (GaussianCompactRiemannName.quadrature GaussianEulerIntegrandName.evaluatorF p
      (H*GaussianCompactRiemannName.mesh t (GaussianEulerCompactModulus.lipschitz R E T) T) a C E (GaussianEulerIntegrandName.fixedData z B))
      (ap2 compactF t (GaussianEulerCompactAdditivity.data z R B a C E T)) one (unit t) := by
  have raw := GaussianCompactMeshIndependence.arbitrary_refinement GaussianEulerIntegrandName.evaluatorF t p H a C E
    (GaussianEulerCompactModulus.lipschitz R E T) T (GaussianEulerIntegrandName.fixedData z B)
    (GaussianEulerCompactAdditivity.compact_input z R B a C E T h) hH hp
  have actual := distance_congr (.eqRefl _)
    (GaussianCompactRiemannName.name_at GaussianEulerIntegrandName.evaluatorF t a C E (GaussianEulerCompactModulus.lipschitz R E T) T _).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ one (unit t) (unit_positive _) (unit_positive t)
    (le_congr (.eqRefl _) (one_mul _).eqSymm (GaussianEulerLowerCofinalQuadrature.three_slack t)) actual

theorem actual_compact_IBP_named_boundary_readback_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (intervalSource (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
      distanceBounded (ap2 boundaryF (var 0) (boundaryData (var 1) (var 3) (var 4) (var 5) (var 6)))
        (GaussianEulerIntegrationByPartsCompact.boundary (var 0) (var 1) (var 3) (var 4) (var 5) (var 6)) (num 6) (unit (var 0))) :=
  closeUniv 8 (.impI (boundary_readback _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsCompactNameObservations
