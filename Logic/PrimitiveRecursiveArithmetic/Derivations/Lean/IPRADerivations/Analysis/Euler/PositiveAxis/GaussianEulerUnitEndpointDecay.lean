import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayFactorBounds
import IPRADerivations.Analysis.Euler.Integration.GaussianEulerDecayQuadraturePrecision
import IPRADerivations.Analysis.Gamma.GaussianGammaCompactQuadratureBoundary

/-!
# Decay endpoint convergence at the original Euler cutoffs

At the exact endpoints of the original varying-cutoff sampler,
the left decay observation is within four dyadic errors of one
and the right is within three of zero at observation precision p.
The actual endpoint subtraction is therefore within seven dyadic
errors of one. The exponent A is an arbitrary positive internal
integer, and neither cutoff is changed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitEndpointDecay

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegrandName (decayPoint)
open GaussianRationalHorner (qzero qadd positive_product)
open GaussianRationalSyntheticDivision (qone qzero_add qadd_sub_cancel)
open GaussianRationalMetric (bounded distanceBounded qsub qnegative qnegative_canonical)
open GaussianRationalReciprocal (bound_congr bounded_negative)
open GaussianRationalDistanceOrder (distance_radius_mono distance_triangle_same distance_congr)
open GaussianReconstructionRoots (distance_zero_iff)
open GaussianEulerDecayMesh (observation observation_rescale)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaIntegralCutoffs (height top etaDen eta_den_positive)
open GaussianGammaCompactQuadratureBoundary (width exact_right_endpoint)
open Syn
open scoped Fm
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem left_decay_rate (E p : PTm n) (h : Γ ⊢[PRAAx] le (unit p) E) :
    Γ ⊢[PRAAx] distanceBounded (observation one E p) qone (num 4) (unit p) := by
  let P := unit p
  let L := observation one E p
  let W := decayPoint one E
  let M := qadd qone W
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have he := le_trans hp h
  have he2 := positive_product E E he he
  have hE2 : Γ ⊢[PRAAx] le P (E*E) :=
    le_trans h (le_congr (by ipra_ring) (.eqRefl _) (mul_le_mul_right E he))
  have compare : Γ ⊢[PRAAx] le ((one*one*P+two*(E*E))*P) (num 3*(E*E*P)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (two*(E*E)*P) (mul_le_mul_right P hE2))
  have error : Γ ⊢[PRAAx] distanceBounded L M (num 3) P :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ he2 hp) hp compare
      (GaussianEulerDecayAddition.original_decay_linear_remainder one E p he he)
  have dist : Γ ⊢[PRAAx] distanceBounded M qone one E :=
    bound_congr (qadd_sub_cancel qone W (qnegative_canonical _)).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianEulerDecayAddition.decay_point_bounded one E he)
  have shift : Γ ⊢[PRAAx] distanceBounded M qone one P :=
    distance_radius_mono _ _ _ _ _ _ he hp (le_congr (by ipra_ring) (by ipra_ring) h) dist
  exact distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ hp error shift)

theorem right_decay_rate (T p : PTm n) (h : Γ ⊢[PRAAx] le p T) :
    Γ ⊢[PRAAx] bounded (observation T one p) (num 3) (unit p) := by
  let P := unit p
  let U := unit T
  have hp : Γ ⊢[PRAAx] le one P := unit_positive p
  have hu : Γ ⊢[PRAAx] le one U := unit_positive T
  have compare : Γ ⊢[PRAAx] le ((P+two*U)*P) (num 3*(U*P)) :=
    le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add_right (two*U*P) (mul_le_mul_right P (GaussianExponentialReference.unit_monotone h)))
  exact GaussianCoefficientNameBounds.bounded_radius_mono _ _ _ _ _
    (positive_product _ _ hu hp) hp compare
    (GaussianEulerDecayFactorBounds.original_integer_decay_bound T p)

theorem endpoint_time (C E T p : PTm n) (he : Γ ⊢[PRAAx] le one E)
    (h : Γ ⊢[PRAAx] one+C ≐ E*T) : Γ ⊢[PRAAx] observation (one+C) E p ≐ observation T one p := by
  have denominator : Γ ⊢[PRAAx] E ≐ one*E := by ipra_ring
  have prepared : Γ ⊢[PRAAx] observation (one+C) E p ≐ observation (T*E) (one*E) p := by
    simpa using Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (observation (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![one+C,E,p]) (σ' := ![T*E,one*E,p]) (fun i => by
        fin_cases i
        · exact h.eqTrans (mul_comm _ _)
        · exact denominator
        · exact .eqRefl p)
  exact prepared.eqTrans (observation_rescale _ _ _ _ (le_refl _) he)

theorem cutoff_endpoint_difference (p s A R : PTm n) (ha : Γ ⊢[PRAAx] le one A)
    (hs : Γ ⊢[PRAAx] le s (p+one)) :
    Γ ⊢[PRAAx] distanceBounded
      (GaussianEulerDecayQuadraturePrecision.endpointDifference one (width p A R) (etaDen p A R) s)
      qone (num 7) (unit s) := by
  let E := etaDen p A R
  let T := top p A R
  let C := width p A R
  let P := unit s
  let X := observation one E s
  let Y := observation (one+C) E s
  have he := eta_den_positive (Γ := Γ) p A R
  have hp := unit_positive (Γ := Γ) s
  have length : Γ ⊢[PRAAx] le (p+one) (height p A R) := by
    unfold height
    exact le_of_eq_add (d := A+GaussianGammaIntegralCutoffs.tailCoefficient R+num 9) (by ipra_ring)
  have shallow := le_trans hs length
  have hEta : Γ ⊢[PRAAx] le P E := GaussianExponentialReference.unit_monotone
    (le_trans shallow (le_congr (by ipra_ring) (.eqRefl _)
      (AnalyticNumberTheory.PhiLower.le_mul_mono ha (le_refl (height p A R)))))
  have hTop : Γ ⊢[PRAAx] le s T := le_trans shallow
    (le_congr (by ipra_ring) (.eqRefl _)
      (AnalyticNumberTheory.PhiLower.le_mul_mono (le_succ_self one) (le_refl (height p A R))))
  have hY : Γ ⊢[PRAAx] bounded Y (num 3) P :=
    bound_congr (endpoint_time C E T s he (exact_right_endpoint _ _ _)).eqSymm (.eqRefl _) (.eqRefl _)
      (right_decay_rate T s hTop)
  have hn := (distance_zero_iff (qnegative Y) (num 3) P hp).iffMpr (bounded_negative Y _ _ hp hY)
  have sum : Γ ⊢[PRAAx] distanceBounded (qsub X Y) (qadd qone qzero) (num 4+num 3) P :=
    GaussianNameArithmetic.sum_distance X qone (qnegative Y) qzero (num 4) (num 3) P hp
    (left_decay_rate E s hEta) hn
  have hcenter : Γ ⊢[PRAAx] qadd (qone : PTm n) qzero ≐ qone :=
    (GaussianRationalLinearProduct.qadd_commutative _ _).eqTrans
      (qzero_add _ (GaussianRationalHorner.ofGaussian_canonical _ _ (le_refl _)))
  have seven : Γ ⊢[PRAAx] num 4+num 3 ≐ num 7 := by ipra_ring
  change Γ ⊢[PRAAx] distanceBounded (qsub X Y) qone (num 7) P
  exact distance_congr (.eqRefl _) hcenter seven (.eqRefl _) sum

theorem original_Euler_decay_cutoff_difference_tends_to_one_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (le one (var 1) ⟶ distanceBounded
        (GaussianEulerDecayQuadraturePrecision.endpointDifference one (width (var 0) (var 1) (var 2))
          (etaDen (var 0) (var 1) (var 2)) (var 0))
        qone (num 7) (unit (var 0))) :=
  closeUniv 3 (.impI (cutoff_endpoint_difference _ _ _ _ Prf.hyp0 (le_add_right _ _)))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitEndpointDecay
