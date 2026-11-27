import IPRADerivations.Analysis.Euler.Integration.Parts.Endpoints.GaussianEulerIntegrationByPartsEndpoints
import IPRADerivations.Analysis.Euler.Integration.Parameters.GaussianEulerPowerInputProperness
import IPRADerivations.Analysis.Gamma.Integrals.CompactQuadrature.GaussianGammaCompactQuadratureBoundary

/-!
# The literal affine-grid endpoint observations

Scaling a positive time numerator and denominator leaves the original
time and decay points unchanged. The original power observations retain
their own evaluation clocks and are compared through their proved
rational-time properness. Multiplication by the actual time and decay
samples gives an explicit comparison for the boundary primitive.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsEndpointRescale

open_ipra
open GaussianEulerIntegrationByPartsLinear (primitive decay originalProduct subst_primitive)
open GaussianEulerIntegrandName (decayF decayData decayPoint powerF powerData)
open GaussianGammaFiniteApproximantName (exponentialInputData)
open GaussianGammaCanonicalExponent (constantF)
open GaussianEulerPowerIncrement (point)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianGammaIntegralCutoffs (etaDen top eta_den_positive top_positive)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianNameEquivalence (cross_to_diagonal diagonal_at)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem fraction_rescale (a b S : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    fraction (a*S) (b*S) ≐ fraction a b :=
  (GaussianEulerDecayFactorBounds.fraction_is_radius_point _ _ (positive_product _ _ hb hS)).eqTrans
    ((GaussianEulerWeightedHalfDecay.radius_rescale a b S hb hS).eqTrans
      (GaussianEulerDecayFactorBounds.fraction_is_radius_point a b hb).eqSymm)

private theorem decay_rescale (p a b S : PTm n)
    (hb : Γ ⊢[PRAAx] le one b) (hS : Γ ⊢[PRAAx] le one S) : Γ ⊢[PRAAx]
    decay p (a*S) (b*S) ≐ decay p a b := by
  have e : Γ ⊢[PRAAx] decayPoint (a*S) (b*S) ≐ decayPoint a b :=
    GaussianInverseBinomialRows.negative_congr (fraction_rescale a b S hb hS)
  have data : Γ ⊢[PRAAx] decayData (a*S) (b*S) ≐ decayData a b := by
    ipra_congr (exponentialInputData constantF (var 0) : PTm 1) with [e] using [decayData, exponentialInputData]
  exact congrAp2 decayF (.eqRefl _) data

theorem original_boundary_rescale (p z B a b S T : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (ha : Γ ⊢[PRAAx] le one a) (hb : Γ ⊢[PRAAx] le one b)
    (hS : Γ ⊢[PRAAx] le one S) (ht : Γ ⊢[PRAAx] le a (T*b)) : Γ ⊢[PRAAx]
    distanceBounded (primitive p z B (a*S) (b*S)) (primitive p z B a b) (num 6*T) (unit p) := by
  let f := fraction a b
  let d := decay p a b
  let w := qmul f d
  have e := GaussianEulerPowerInputProperness.original_power_proper z B (a*S) (b*S) a b hB
    (.andI (positive_product _ _ ha hS) (positive_product _ _ hb hS)) (.andI ha hb) (by ipra_ring)
  have near : Γ ⊢[PRAAx] distanceBounded (point p z B (a*S) (b*S)) (point p z B a b) two (unit p) :=
    diagonal_at _ _ _ _ p (cross_to_diagonal _ _ _ _ e)
  have raw := bounded_product f d T one GaussianNameRingLaws.three one (le_refl one) (le_refl one)
    (GaussianEulerExponentCompactBounds.fraction_bound a b T hb ht)
    (GaussianEulerDecayIncrement.decay_observation_uniform_bound a b p ha hb)
  have hw : Γ ⊢[PRAAx] bounded w (num 3*T) one :=
    bound_congr (.eqRefl _) (by unfold GaussianNameRingLaws.three; ipra_ring) (by ipra_ring) raw
  have left : Γ ⊢[PRAAx] primitive p z B (a*S) (b*S) ≐ qmul w (point p z B (a*S) (b*S)) :=
    (qmul_congr (fraction_rescale a b S hb hS) (qmul_congr (.eqRefl _) (decay_rescale p a b S hb hS))).eqTrans
      (GaussianApproximateInverseDistance.left_rearrange f d _)
  have right : Γ ⊢[PRAAx] primitive p z B a b ≐ qmul w (point p z B a b) :=
    GaussianApproximateInverseDistance.left_rearrange f d _
  exact distance_congr left.eqSymm right.eqSymm (by ipra_ring) (.eqRefl _)
    (GaussianApproximateInverseDistance.multiply_distance w _ _ _ _ _ (unit_positive p) hw near)

private theorem primitive_time_congr (p z B a a' b b' : PTm n)
    (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') : Γ ⊢[PRAAx]
    primitive p z B a b ≐ primitive p z B a' b' := by
  ipra_congr (primitive (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5) with
    [.eqRefl p, .eqRefl z, .eqRefl B, ha, hb]

theorem original_affine_cutoff_endpoints (p z R B k A N : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    distanceBounded (primitive p z B (one*N) (etaDen k A R*N)) (primitive p z B one (etaDen k A R)) (num 6) (unit p) ⋏
    distanceBounded (primitive p z B (one*N+width k A R*N) (etaDen k A R*N))
      (primitive p z B (top k A R) one) (num 6*top k A R) (unit p) := by
  let E := etaDen k A R
  let T := top k A R
  let C := width k A R
  have hE : Γ ⊢[PRAAx] le one E := eta_den_positive k A R
  have hT : Γ ⊢[PRAAx] le one T := top_positive k A R
  have hS := positive_product _ _ hE hN
  have lo := original_boundary_rescale p z B one E N one hB (le_refl one) hE hN
    (le_congr (.eqRefl _) (by ipra_ring) hE)
  have hi := original_boundary_rescale p z B T one (E*N) T hB hT (le_refl one) hS
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl T))
  have na : Γ ⊢[PRAAx] T*(E*N) ≐ one*N+C*N := by
    have e := natEq (exact_right_endpoint (Γ := Γ) k A R)
    apply deriveNat
    dsimp only [T,E,C]
    ipra_simps
    linear_combination -(Groth.ι (Q.mk Γ N))*e
  exact .andI (distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) lo)
    (distance_congr (primitive_time_congr _ _ _ _ _ _ _ na (by ipra_ring)) (.eqRefl _) (.eqRefl _) (.eqRefl _) hi)

theorem actual_integration_by_parts_affine_cutoff_endpoints_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 3) ⋏ le one (var 6)) ⟶
      distanceBounded (primitive (var 0) (var 1) (var 3) (one*var 6) (etaDen (var 4) (var 5) (var 2)*var 6))
        (primitive (var 0) (var 1) (var 3) one (etaDen (var 4) (var 5) (var 2))) (num 6) (unit (var 0)) ⋏
      distanceBounded (primitive (var 0) (var 1) (var 3) (one*var 6+width (var 4) (var 5) (var 2)*var 6)
        (etaDen (var 4) (var 5) (var 2)*var 6)) (primitive (var 0) (var 1) (var 3) (top (var 4) (var 5) (var 2)) one)
        (num 6*top (var 4) (var 5) (var 2)) (unit (var 0))) :=
  closeUniv 7 (.impI (original_affine_cutoff_endpoints _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegrationByPartsEndpointRescale
