import IPRADerivations.Analysis.Stirling.Binet.Kernel.HyperbolicForm.ImaginaryRatios.GaussianBinetKernelFrozenHyperbolic
import IPRADerivations.Analysis.Euler.Integration.Decay.Quadrature.GaussianEulerDecayQuadratureAtZero

/-!
# Products of the fixed Binet half-time exponentials

The original exponential addition theorem gives the full-time decay
from the square of the negative half-time exponential, and one from
the product of the opposite signed half-time exponentials.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianBinetKernelHalfExponential

open_ipra
open GaussianBinetKernelFrozenHyperbolic (halfTime fixedExpF fixedExpData expRadius fixed_exp_input)
open GaussianBoundedConstantProductName (constantF constant_at constant_regular)
open GaussianEulerDecayMesh (observation)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaFiniteApproximantName (exponential_input)
open GaussianNameArithmetic (multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans)
open GaussianNamedGammaHalfShift (constant_sum)
open GaussianPiRationalScale (point point_add point_negate subst_point)
open GaussianRationalHorner (positive_product qadd qzero)
open GaussianRationalMetric (qnegative)
open GaussianRationalSyntheticDivision (qadd_congr qone)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "FE" => GaussianGammaFoldedApproximantBalance.exponential_product_equivalent

theorem negative_point (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] point true A B ≐ decayPoint A B := by
  have e : Γ ⊢[PRAAx] point false A B ≐ GaussianPositiveRationalLogarithm.fraction A B :=
    (GaussianEulerDecayFactorBounds.fraction_is_radius_point A B hB).eqSymm
  exact (point_negate false A B hB).eqSymm.eqTrans (GaussianInverseBinomialRows.negative_congr e)

private theorem twice_negative_argument (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (halfTime true A B) (halfTime true A B) ≐ decayPoint A B := by
  have h2 := le_succ_self (Γ := Γ) one
  have h2B := positive_product _ _ h2 hB
  have e : Γ ⊢[PRAAx] point true (A+A) (two*B) ≐ point true (two*A) (two*B) := by
    simpa only [subst_point,Syn.subst_var,Matrix.cons_val_zero,Matrix.cons_val_one] using
      Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (point true (var 0) (var 1) : PTm 2)
        (σ := ![A+A,two*B]) (σ' := ![two*A,two*B]) (fun i => by
          fin_cases i
          · exact (show Γ ⊢[PRAAx] A+A ≐ two*A by ipra_ring)
          · exact .eqRefl _)
  change Γ ⊢[PRAAx] qadd (point true A (two*B)) (point true A (two*B)) ≐ decayPoint A B
  have sum : Γ ⊢[PRAAx] qadd (point true A (two*B)) (point true A (two*B)) ≐ point true (A+A) (two*B) :=
    point_add true A (two*B) A h2B
  have scale : Γ ⊢[PRAAx] point true (two*A) (two*B) ≐ point true A B :=
    GaussianPiRationalScaleRepresentation.point_rescale true A B two hB h2
  exact sum.eqTrans (e.eqTrans (scale.eqTrans (negative_point A B hB)))

private theorem opposite_arguments (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx]
    qadd (halfTime true A B) (halfTime false A B) ≐ decayPoint zero one := by
  let q := halfTime false A B
  have h2B := positive_product _ _ (le_succ_self (Γ := Γ) one) hB
  have left : Γ ⊢[PRAAx] halfTime true A B ≐ qnegative q := (point_negate false A (two*B) h2B).eqSymm
  have zeroPoint : Γ ⊢[PRAAx] decayPoint zero one ≐ qzero :=
    (GaussianInverseBinomialRows.negative_congr (GaussianGammaRationalWendelBoundary.fraction_zero one (le_refl one))).eqTrans
      GaussianEulerBetaPrimitiveEvaluationPascal.negative_zero
  exact (qadd_congr left (.eqRefl q)).eqTrans ((GaussianReciprocalHorner.qadd_commutative (qnegative q) q).eqTrans
    ((GaussianCoefficientNormOrder.qsub_self q).eqTrans zeroPoint.eqSymm))

theorem half_square (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF fixedExpF fixedExpF) decayF
      (multiplyData fixedExpF fixedExpF (fixedExpData true A B) (fixedExpData true A B)) (decayData A B) :=
  FE constantF constantF constantF (expRadius A) (expRadius A) (GaussianNameBounds.U constantF (decayPoint A B))
    (halfTime true A B) (halfTime true A B) (decayPoint A B)
    (fixed_exp_input true A B hB) (fixed_exp_input true A B hB) (exponential_input _ _ (constant_regular _))
    (constant_sum _ _ _ (twice_negative_argument A B hB))

theorem zero_decay_cross : Γ ⊢[PRAAx] crossEquivalent decayF constantF (decayData (zero : PTm n) one) qone := by
  apply GaussianNameConjugation.equal_samples_cross _ _ _ _
    (GaussianEulerDecayQuadraturePrecision.observation_regular zero one) (constant_regular _)
  refine .allI ?_
  have z := GaussianEulerDecayQuadratureAtZero.zero_observation (Γ := Γ.map Fm.shift)
    one (var 0) (le_refl one)
  have same : Γ.map Fm.shift ⊢[PRAAx] observation zero one (var 0) ≐ ap2 constantF (var 0) qone :=
    z.eqTrans (constant_at _ _).eqSymm
  simpa only [GaussianNameConjugation.pointwiseEqual,observation,Syn.shift,decayData,
    GaussianGammaFiniteApproximantName.exponentialInputData,GaussianRadiusExponentialName.subst_data,
    GaussianNameBounds.subst_U,GaussianEulerIntegrandName.subst_decayPoint,GaussianRationalSyntheticDivision.subst_qone,
    one,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero] using same

theorem half_mixed (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF fixedExpF fixedExpF) constantF
      (multiplyData fixedExpF fixedExpF (fixedExpData true A B) (fixedExpData false A B)) qone := by
  have add := FE constantF constantF constantF (expRadius A) (expRadius A)
    (GaussianNameBounds.U constantF (decayPoint (zero : PTm n) one))
    (halfTime true A B) (halfTime false A B) (decayPoint zero one)
    (fixed_exp_input true A B hB) (fixed_exp_input false A B hB) (exponential_input _ _ (constant_regular _))
    (constant_sum _ _ _ (opposite_arguments A B hB))
  exact cross_trans _ _ _ _ _ _ add zero_decay_cross

theorem actual_Binet_half_exponential_products_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 1) ⟶
      (crossEquivalent (multiplyF fixedExpF fixedExpF) decayF
        (multiplyData fixedExpF fixedExpF (fixedExpData true (var 0) (var 1)) (fixedExpData true (var 0) (var 1)))
        (decayData (var 0) (var 1)) ⋏
       crossEquivalent (multiplyF fixedExpF fixedExpF) constantF
        (multiplyData fixedExpF fixedExpF (fixedExpData true (var 0) (var 1)) (fixedExpData false (var 0) (var 1))) qone)) :=
  closeUniv 2 (.impI (.andI (half_square _ _ Prf.hyp0) (half_mixed _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBinetKernelHalfExponential
