import IPRADerivations.Analysis.Euler.PositiveAxis.HalfDecay.GaussianEulerHalfDecayTailBound
import IPRADerivations.Analysis.Euler.CompactExhaustion.GaussianEulerCompactUpperTail

/-!
# Weighted half-decay quadratures retain one literal endpoint coefficient

An actual bound on K times the original left decay observation gives
the same bound on K times its endpoint difference, with the original
endpoint observation error. For the factorial half-decay quadrature,
K is exactly D_R=2 M_R, including the original factor two from integration.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianWeightedHalfDecayEndpoint

open_ipra
open GaussianEulerWeightedHalfDecay (majorant radius_reciprocal)
open GaussianEulerDecayMesh (observation)
open GaussianEulerDecayQuadraturePrecision (endpointDifference)
open GaussianEulerCompactUpperTail (halfEvaluator)
open GaussianRationalHorner (qmul positive_product)
open GaussianRationalMetric (bounded)
open GaussianRationalReciprocal (bound_congr bounded_product)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianDominantPairAlgebra (radiusPoint radius_bounded radius_multiply radius_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def coefficient (R : PTm n) : PTm n := GaussianGammaIntegralCutoffs.tailCoefficient R
theorem coefficient_identity (R : PTm n) : Γ ⊢[PRAAx] coefficient R ≐ two*majorant R := by
  unfold coefficient GaussianGammaIntegralCutoffs.tailCoefficient majorant unit
  exact (congrMul (pw_succ two R) (.eqRefl _)).eqTrans (by ipra_ring)
theorem coefficient_positive (R : PTm n) : Γ ⊢[PRAAx] le one (coefficient R) :=
  positive_product _ _ (unit_positive _) (GaussianRationalPolynomialExponential.factorial_positive R)

theorem weighted_endpoint_bound (K a C E q A B : PTm n) (hK : Γ ⊢[PRAAx] le one K)
    (hE : Γ ⊢[PRAAx] le one E) (hB : Γ ⊢[PRAAx] le one B)
    (hStart : Γ ⊢[PRAAx] bounded (qmul (radiusPoint K one) (observation a E q)) A B) : Γ ⊢[PRAAx]
    bounded (qmul (radiusPoint K one) (endpointDifference a C E q))
      (A*unit q+num 6*K*B) (B*unit q) := by
  let x := observation a E q
  let r := radiusPoint one K
  let w := radiusPoint K one
  have inv := bounded_product r (qmul w x) one K A B hK hB (radius_bounded one K hK) hStart
  have same : Γ ⊢[PRAAx] qmul r (qmul w x) ≐ x :=
    (GaussianReciprocalHorner.qmul_associative r w x).eqSymm.eqTrans
      ((GaussianRationalSyntheticDivision.qmul_congr (radius_reciprocal K one hK (le_refl one)) (.eqRefl _)).eqTrans
        (GaussianPolynomialDeterminantTerms.one_mul_canonical x (GaussianRadiusExponentialName.sample_canonical _ _ _ _)))
  have start : Γ ⊢[PRAAx] bounded x A (B*K) :=
    bound_congr same (one_mul A) (mul_comm _ _) inv
  have endpointBound := GaussianEulerDecayEndpointBound.endpoint_norm a C E q A (B*K) hE (positive_product _ _ hB hK) start
  have raw := bounded_product w (endpointDifference a C E q) K one _ _ (le_refl one)
    (positive_product _ _ (positive_product _ _ hB hK) (unit_positive q)) (radius_bounded K one (le_refl one)) endpointBound
  exact bounded_radius_mono _ _ _ _ _ (positive_product _ _ (le_refl one)
      (positive_product _ _ (positive_product _ _ hB hK) (unit_positive q))) (positive_product _ _ hB (unit_positive q))
    (le_of_eq_add (d := zero) (by ipra_ring)) raw

theorem original_endpoint_factor (R x : PTm n) : Γ ⊢[PRAAx]
    qmul (radiusPoint (majorant R) one) (qmul (GaussianRationalNaturalScale.naturalPoint two) x) ≐
      qmul (radiusPoint (coefficient R) one) x := by
  have twoPoint := GaussianEulerDecayFactorBounds.fraction_is_radius_point (Γ := Γ) two one (le_refl one)
  have radius := (radius_multiply (majorant R) one two one (le_refl (Γ := Γ) one) (le_refl one)).eqTrans
    (radius_congr ((mul_comm _ _).eqTrans (coefficient_identity R).eqSymm) (one_mul one))
  exact (GaussianRationalSyntheticDivision.qmul_congr (.eqRefl _)
    (GaussianRationalSyntheticDivision.qmul_congr twoPoint (.eqRefl _))).eqTrans
    ((GaussianReciprocalHorner.qmul_associative _ _ _).eqSymm.eqTrans
      (GaussianRationalSyntheticDivision.qmul_congr radius (.eqRefl _)))

def meshNumerator (p q M C E : PTm n) : PTm n := GaussianEulerDecayQuadraturePrecision.numerator p q M C (two*E)
def meshDenominator (p q M E : PTm n) : PTm n := GaussianEulerDecayQuadraturePrecision.denominator p q M (two*E)
def numerator (p q M C E R A B : PTm n) : PTm n :=
  (coefficient R*meshNumerator p q M C E)*(B*unit q)+(A*unit q+num 6*coefficient R*B)*meshDenominator p q M E
def denominator (p q M E B : PTm n) : PTm n := meshDenominator p q M E*(B*unit q)

theorem mesh_denominator_positive (p q M E : PTm n) (hM : Γ ⊢[PRAAx] le one M) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    le one (meshDenominator p q M E) :=
  positive_product _ _ (positive_product _ _ (positive_product _ _
    (positive_product _ _ (positive_product _ _ (le_succ_self one) hE) (positive_product _ _ (le_succ_self one) hE)) hM)
      (unit_positive p)) (unit_positive q)

/-- The leading bound is exactly that of D_R times the actual left
decay observation, not two separately estimated tail integrals. -/
theorem original_scaled_half_decay_bound (p q M a C E R A B : PTm n)
    (ha : Γ ⊢[PRAAx] le one a) (hM : Γ ⊢[PRAAx] le one M) (hC : Γ ⊢[PRAAx] le one C)
    (hE : Γ ⊢[PRAAx] le one E) (hstep : Γ ⊢[PRAAx] le C ((two*E)*M))
    (hB : Γ ⊢[PRAAx] le one B)
    (hStart : Γ ⊢[PRAAx] bounded (qmul (radiusPoint (coefficient R) one) (observation a (two*E) q)) A B) : Γ ⊢[PRAAx]
    bounded (qmul (radiusPoint (majorant R) one) (GaussianCompactRiemannName.quadrature halfEvaluator p M a C E zero))
      (numerator p q M C E R A B) (denominator p q M E B) := by
  have hd := mesh_denominator_positive p q M E hM hE
  have h2E := positive_product (Γ := Γ) _ _ (le_succ_self one) hE
  have raw := GaussianApproximateInverseDistance.multiply_distance (radiusPoint (majorant R) one) _ _ (majorant R)
    (two*meshNumerator p q M C E) (meshDenominator p q M E) hd (radius_bounded _ one (le_refl one))
    (GaussianEulerHalfDecayQuadrature.half_decay_independent_endpoint p q M a C E zero ha hM hE hC hstep)
  have dist : Γ ⊢[PRAAx] GaussianRationalMetric.distanceBounded
      (qmul (radiusPoint (majorant R) one) (GaussianCompactRiemannName.quadrature halfEvaluator p M a C E zero))
      (qmul (radiusPoint (coefficient R) one) (endpointDifference a C (two*E) q))
      (coefficient R*meshNumerator p q M C E) (meshDenominator p q M E) :=
    GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (original_endpoint_factor R (endpointDifference a C (two*E) q))
    (by
      apply deriveNat
      have eq := natEq (coefficient_identity (Γ := Γ) R)
      ipra_simps
      rw [eq]
      ring) (.eqRefl _) raw
  have endpoint := weighted_endpoint_bound (coefficient R) a C (two*E) q A B (coefficient_positive R) h2E hB hStart
  exact GaussianReconstructionRoots.norm_from_distance _ _ _ _ _ _ hd
    (positive_product _ _ hB (unit_positive q)) dist endpoint

theorem actual_weighted_decay_endpoint_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    ((le one (var 0) ⋏ le one (var 3) ⋏ le one (var 6)) ⟶
      bounded (qmul (radiusPoint (var 0) one) (observation (var 1) (var 3) (var 4))) (var 5) (var 6) ⟶
      bounded (qmul (radiusPoint (var 0) one) (endpointDifference (var 1) (var 2) (var 3) (var 4)))
        ((var 5)*unit (var 4)+num 6*(var 0)*(var 6)) ((var 6)*unit (var 4))) :=
  closeUniv 7 (.impI (.impI (weighted_endpoint_bound _ _ _ _ _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

theorem original_half_decay_grid_one_weighted_endpoint_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
    ((le one (var 3) ⋏ le one (var 2) ⋏ le one (var 4) ⋏ le one (var 5) ⋏
        le (var 4) ((two*var 5)*var 2) ⋏ le one (var 8)) ⟶
      bounded (qmul (radiusPoint (coefficient (var 6)) one) (observation (var 3) (two*var 5) (var 1))) (var 7) (var 8) ⟶
      bounded (qmul (radiusPoint (majorant (var 6)) one)
        (GaussianCompactRiemannName.quadrature halfEvaluator (var 0) (var 2) (var 3) (var 4) (var 5) zero))
        (numerator (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) (var 8))
        (denominator (var 0) (var 1) (var 2) (var 5) (var 8))) :=
  closeUniv 9 (.impI (.impI (original_scaled_half_decay_bound _ _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂.andE₁
    Prf.hyp1.andE₂.andE₂.andE₂.andE₂.andE₁ Prf.hyp1.andE₂.andE₂.andE₂.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianWeightedHalfDecayEndpoint
