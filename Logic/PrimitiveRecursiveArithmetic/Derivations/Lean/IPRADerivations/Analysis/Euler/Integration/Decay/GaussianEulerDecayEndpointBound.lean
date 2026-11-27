import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadraturePrecision
import IPRADerivations.Analysis.Euler.Integration.Decay.GaussianEulerDecayOrder

/-!
# A one-sided majorant for the original decay endpoint difference

Positive representatives let the right endpoint be subtracted without
charging a second copy of the left-endpoint norm. The original endpoint
difference is bounded by the left observation's bound plus six dyadic
observation errors, on every positive rational compact interval.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerDecayEndpointBound

open_ipra
open GaussianEulerIntegrandName (decayF decayData)
open GaussianEulerDecayMesh (observation)
open GaussianEulerDecayQuadraturePrecision (endpointDifference)
open GaussianEulerDecayOrder (signedTime original_decay_order original_decay_nonnegative_representative)
open GaussianRealExponentialPositiveRepresentative (positiveF positiveData sample_canonical sample_nonnegative)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (canonical positive_product qzero)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalReciprocal (bound_congr bounded_negative)
open GaussianReconstructionRoots (distance_zero_iff norm_from_distance)
open RationalGaussianEmbedding (scalarZero scalar_zero_represents canonical_axis_roundtrip embed_zero)
open RationalValueBounds (upper upper_of_radius upper_order_right radius_of_upper upper_mono)
open GaussianPositiveRealArithmetic (positive sign)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem scalar_nonnegative (x : PTm n) (hx : Γ ⊢[PRAAx] sign x) :
    Γ ⊢[PRAAx] RationalArgmin.rationalLE scalarZero x :=
  GaussianRationalMetric.comparison_of_cleared scalarZero x zero
    (GaussianPositiveRealArithmetic.numerator x) one (denominatorOf x)
    (le_refl one) (RationalArgmin.denominator_positive x) (scalar_zero_represents one)
    (GaussianPositiveRealArithmetic.natural_representation x hx)
    (le_congr (mul_zero _).eqSymm (.eqRefl _) (zero_le _))

theorem positive_difference_bound (u v A B : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hu : Γ ⊢[PRAAx] canonical u) (hv : Γ ⊢[PRAAx] canonical v)
    (hp : Γ ⊢[PRAAx] RationalGaussianEmbedding.axis u) (hq : Γ ⊢[PRAAx] positive v)
    (hbound : Γ ⊢[PRAAx] bounded u A B) (horder : Γ ⊢[PRAAx] upper (fstT v) (fstT u) A B) :
    Γ ⊢[PRAAx] bounded (qsub u v) A B := by
  have pu := canonical_axis_roundtrip u hu hp
  have pv := canonical_axis_roundtrip v hv hq.andE₁
  have near := (distance_zero_iff u A B hB).iffMpr hbound
  have scalar := GaussianGammaRealValues.scalar_radius_of_embedded_distance (fstT u) scalarZero A B hB
    (distance_congr pu.eqSymm embed_zero.eqSymm (.eqRefl _) (.eqRefl _) near)
  have order := upper_order_right (fstT u) scalarZero (fstT v) A B
    (upper_of_radius _ _ _ _ scalar) (scalar_nonnegative _ hq.andE₂)
  exact distance_congr pu pv (.eqRefl _) (.eqRefl _)
    (RationalGaussianNameEmbedding.distance_from_radius (fstT u) (fstT v) A B hB
      (radius_of_upper _ _ _ _ order horder))

private def representative (a E p : PTm n) : PTm n := ap2 positiveF p (positiveData (signedTime a E))

private theorem representative_error (a E p : PTm n) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] distanceBounded (representative a E p) (observation a E p) two (unit p) := by
  have h := GaussianNameEquivalence.cross_at positiveF decayF
    (positiveData (signedTime a E)) (decayData a E) p p (original_decay_nonnegative_representative a E hE)
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ (unit_positive p) (unit_positive p))
    (unit_positive p) (le_of_eq_add (d := zero) (by ipra_ring)) h

private theorem representative_order (a C E p : PTm n) (hE : Γ ⊢[PRAAx] le one E) :
    Γ ⊢[PRAAx] upper (fstT (representative (a+C) E p)) (fstT (representative a E p))
      (unit p+unit p) (unit p*unit p) := by
  have hl := original_decay_nonnegative_representative a E hE
  have hr := original_decay_nonnegative_representative (a+C) E hE
  have cmp : Γ ⊢[PRAAx] le (a*E) ((a+C)*E) := mul_le_mul_right E (le_add_right a C)
  exact GaussianNamedRealOrderTransport.transport_at positiveF decayF decayF positiveF _ _ _ _ p p hr
    (GaussianNameEquivalence.cross_symm _ _ _ _ hl) (original_decay_order a E (a+C) E hE hE cmp)

theorem endpoint_norm (a C E p A B : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hB : Γ ⊢[PRAAx] le one B) (hbound : Γ ⊢[PRAAx] bounded (observation a E p) A B) :
    Γ ⊢[PRAAx] bounded (endpointDifference a C E p) (A*unit p+num 6*B) (B*unit p) := by
  let P := unit p
  let L := representative a E p
  let R := representative (a+C) E p
  let X := observation a E p
  let Y := observation (a+C) E p
  let D := B*P
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hd : Γ ⊢[PRAAx] le one D := positive_product B P hB hp
  have hn : Γ ⊢[PRAAx] bounded L (A*P+two*B) D :=
    bound_congr (.eqRefl _) (by ipra_ring) (by dsimp only [D]; ipra_ring)
      (norm_from_distance L X two P A B hp hB (representative_error a E p hE) hbound)
  have ord : Γ ⊢[PRAAx] upper (fstT R) (fstT L) (A*P+two*B) D :=
    upper_mono _ _ (P+P) (P*P) _ _ (positive_product P P hp hp) (representative_order a C E p hE)
      (le_of_eq_add (d := A*P*P*P) (by dsimp only [D]; ipra_ring))
  have hb := positive_difference_bound L R _ D hd (sample_canonical (signedTime a E) p)
    (sample_canonical (signedTime (a+C) E) p) (sample_nonnegative (signedTime a E) p).andE₁
    (sample_nonnegative (signedTime (a+C) E) p) hn ord
  have first : Γ ⊢[PRAAx] distanceBounded X L (two*B) D :=
    distance_radius_mono _ _ _ _ _ _ hp hd (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      (distance_symmetric _ _ _ _ hp (representative_error a E p hE))
  have second : Γ ⊢[PRAAx] distanceBounded Y R (two*B) D :=
    distance_radius_mono _ _ _ _ _ _ hp hd (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      (distance_symmetric _ _ _ _ hp (representative_error (a+C) E p hE))
  have neg := bound_congr (GaussianCharacteristicEntryNorm.negative_difference Y R).eqSymm (.eqRefl _) (.eqRefl _)
    (bounded_negative (qsub Y R) _ _ hd second)
  have pair := GaussianNameArithmetic.sum_distance _ _ _ _ _ _ _ hd first neg
  exact (distance_zero_iff _ _ _ hd).iffMp
    (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hd pair ((distance_zero_iff _ _ _ hd).iffMpr hb)))

theorem original_decay_endpoint_norm_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6
    ((le one (var 2) ⋏ le one (var 5)) ⟶ bounded (observation (var 0) (var 2) (var 3)) (var 4) (var 5) ⟶
      bounded (endpointDifference (var 0) (var 1) (var 2) (var 3))
        (var 4*unit (var 3)+num 6*var 5) (var 5*unit (var 3))) :=
  closeUniv 6 (.impI (.impI (endpoint_norm _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianEulerDecayEndpointBound
