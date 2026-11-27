import IPRADerivations.Analysis.Stirling.Binet.WeightedIntegrals.Exponential.GaussianBinetWeightedExponentialUniform

/-!
# Uniform size of the original weighted Binet sampler

The original one-panel quadrature reads the zero tag, giving exactly
one half at every observation clock. The finite readback estimate
then bounds the cofinal observation throughout the time horizon.
-/

set_option autoImplicit false
set_option maxHeartbeats 500000

namespace LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialBound

open_ipra
open GaussianBinetWeightedExponentialAlgebra (tagWeight)
open GaussianBinetWeightedExponentialGrid (cell_at evaluatorF rowValue value zero_observation)
open GaussianBinetWeightedExponentialRowRate (gain)
open GaussianBinetWeightedExponentialUniform (finite_readback readBudget)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (sampleBody sampleData)
open GaussianEulerDecayMesh (observation_numerator_congr)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (ofGaussian_canonical qzero positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qadd_congr qmul_congr qone qsub_congr qzero_add)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

def radius (T : PTm n) : PTm n := two*gain T+num 9

ipra_subst radius [two]

theorem one_panel (p a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] value p one a b ≐ fraction one two := by
  let f := sampleBody evaluatorF
  let x := sampleData p one one one one (pairT a b)
  let c : PTm n := fraction one two
  have hc : Γ ⊢[PRAAx] GaussianRationalHorner.canonical c := ofGaussian_canonical _ _ (le_succ_self one)
  have w : Γ ⊢[PRAAx] tagWeight zero one ≐ c :=
    (qsub_congr (.eqRefl c) (GaussianGammaRationalWendelBoundary.fraction_zero one (le_refl one))).eqTrans
      ((qadd_congr (.eqRefl _) GaussianEulerBetaPrimitiveEvaluationPascal.negative_zero).eqTrans
        ((GaussianReciprocalHorner.qadd_commutative c qzero).eqTrans (qzero_add c hc)))
  have e := (observation_numerator_congr (a*zero) zero (b*one) p (mul_zero a)).eqTrans
    (zero_observation (b*one) p (positive_product _ _ hb (le_refl one)))
  have row : Γ ⊢[PRAAx] rowValue p a b zero one ≐ c :=
    (qmul_congr w e).eqTrans (GaussianReciprocalHorner.qmul_one_right c hc)
  have grid : Γ ⊢[PRAAx] sum f one x ≐ c :=
    GaussianRationalFiniteSum.sum_singleton f x ((cell_at zero p one a b).eqTrans row) hc
  have scale : Γ ⊢[PRAAx] weight one one one ≐ qone :=
    (GaussianCompactRiemannName.fraction_congr one one (one*one) one (.eqRefl _) (one_mul _)).eqTrans
      ((GaussianEulerDecayFactorBounds.fraction_is_radius_point one one (le_refl one)).eqTrans
        GaussianDominantPairAlgebra.radius_one)
  exact (qmul_congr scale grid).eqTrans
    ((GaussianRationalPowerAlgebra.qmul_commutative _ _).eqTrans (GaussianReciprocalHorner.qmul_one_right c hc))

theorem observation_bound (p a b T : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hT : Γ ⊢[PRAAx] le a (T*b)) :
    Γ ⊢[PRAAx] bounded
      (ap2 GaussianBinetWeightedExponential.nameF p (GaussianBinetWeightedExponential.data a b)) (radius T) one := by
  let X := ap2 GaussianBinetWeightedExponential.nameF p (GaussianBinetWeightedExponential.data a b)
  let c : PTm n := fraction one two
  let K := two*gain T+num 8
  have hU := unit_positive (Γ := Γ) p
  have d := distance_congr (.eqRefl _) (one_panel p a b hb) (.eqRefl _) (one_mul (unit p))
    (finite_readback p one a b T (le_refl one) hb hT)
  have first : Γ ⊢[PRAAx] distanceBounded X c K one := by
    apply distance_radius_mono _ _ _ _ _ _ hU (le_refl one) ?_ d
    dsimp only [readBudget,K]
    ipra_le 𝔞(gain T+num 8)*sl hU
  have hc : Γ ⊢[PRAAx] bounded c one one :=
    GaussianEulerExponentCompactBounds.fraction_bound _ _ _ (le_succ_self one)
      (le_congr (.eqRefl _) (one_mul _).eqSymm (le_succ_self one))
  have second := (GaussianReconstructionRoots.distance_zero_iff c one one (le_refl one)).iffMpr hc
  apply (GaussianReconstructionRoots.distance_zero_iff X (radius T) one (le_refl one)).iffMp
  exact distance_congr (.eqRefl _) (.eqRefl _) (by dsimp only [radius,K]; ipra_ring) (.eqRefl _)
    (distance_triangle_same _ _ _ _ _ _ (le_refl one) first second)

theorem actual_weighted_Binet_observation_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (le one (var 2) ⟶ le (var 1) (var 3*var 2) ⟶
      bounded (ap2 GaussianBinetWeightedExponential.nameF (var 0)
        (GaussianBinetWeightedExponential.data (var 1) (var 2))) (radius (var 3)) one) :=
  closeUniv 4 (.impI (.impI (observation_bound _ _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetWeightedExponentialBound
