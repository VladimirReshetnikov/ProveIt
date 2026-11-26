import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.GaussianGammaNegativeIntervalStep
import IPRADerivations.Analysis.Gamma.NegativeAxis.Input.GaussianGammaNegativeIntervalRescale
import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalRescale
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Products.GaussianGammaNegativeProductDerivativeCorrection
import IPRADerivations.Analysis.Gamma.NegativeAxis.Derivatives.Products.GaussianGammaNegativeProductDerivativeRate

/-!
# Exact shift-product coefficients at a native unit step

Rescale the base rational to the neighbor denominator to use the
literal divided difference. Both its exact variation identity and its
limit coefficient refer to the original unscaled product.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalStepCoefficient

open_ipra
open ComplexLogarithmRemainder (oneCode)
open GaussianGammaNegativeCriticalCorrection (correction guard)
open GaussianGammaNegativeIntervalNative (product)
open GaussianGammaNegativeIntervalRescale (guard_rescale original_product_rescale)
open GaussianGammaNegativeIntervalStep (numerator denominator denominator_positive neighbor_guard)
open GaussianGammaNegativeProductDerivative (dividedDifference original_product_gap)
open GaussianGammaNegativeProductDerivativeCorrection (original_first_coefficient)
open GaussianGammaNegativeProductDerivativeRate (derivativeCost derivative_error)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr)
open GaussianRationalHorner (ofGaussian positive_product qmul)
open GaussianRationalMetric (distanceBounded qsub qnegative)
open GaussianRationalReciprocal (bound_congr)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open GaussianStirlingGammaLogarithm (arg)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def neighborProduct (a b N D : PTm n) : PTm n := product (numerator a b D) (denominator b D) N
def finiteCoefficient (a b N D : PTm n) : PTm n :=
  dividedDifference (arg (D*a)) (arg (numerator a b D)) (denominator b D) (succ N)
def limitCoefficient (a b N : PTm n) : PTm n := qmul (product a b N) (qnegative (correction a b N))

theorem exact_step (a b D : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    qsub (fraction (numerator a b D) (denominator b D)) (fraction (D*a) (denominator b D)) ≐ ofGaussian oneCode D := by
  have hdb := positive_product (Γ := Γ) _ _ hD hb
  have left := GaussianCompactRiemannName.fraction_congr (Γ := Γ) (numerator a b D)
    (GaussianGammaDigammaStep.neighborNumerator a b D) (denominator b D) (GaussianGammaDigammaStep.neighborDenominator b D)
    (.eqRefl _) (mul_comm _ _)
  have right := GaussianStirlingRationalTelescopers.fraction_same (D*a) (denominator b D) a b hdb hb
    (by unfold denominator; ipra_ring)
  exact (qsub_congr left right).eqTrans (GaussianGammaDigammaStep.coefficient_difference a b D hb hD)

theorem step_bound (a b D : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] distanceBounded (fraction (numerator a b D) (denominator b D)) (fraction (D*a) (denominator b D)) one D :=
  bound_congr ((exact_step a b D hb hD).eqTrans (GaussianGammaDigammaStep.unit_step_value D hD).eqSymm).eqSymm
    (.eqRefl _) (.eqRefl _)
    (bound_congr (GaussianEulerDecayFactorBounds.fraction_is_radius_point one D hD).eqSymm (.eqRefl _) (.eqRefl _)
      (GaussianDominantPairAlgebra.radius_bounded one D hD))

theorem exact_product_step (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hr : Γ ⊢[PRAAx] lt b D) : Γ ⊢[PRAAx]
    qsub (neighborProduct a b N D) (product a b N) ≐ qmul (ofGaussian oneCode D) (finiteCoefficient a b N D) := by
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  have hD := denominator_positive h hr
  have hbD := positive_product (Γ := Γ) _ _ hD hb
  exact (qsub_congr (.eqRefl _) (original_product_rescale a b D N h hD).eqSymm).eqTrans
    ((original_product_gap (arg (D*a)) (arg (numerator a b D)) (denominator b D) (succ N) hbD).eqTrans
      (qmul_congr (exact_step a b D hb hD) (.eqRefl _)))

theorem finite_coefficient_rate (a b N D : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hr : Γ ⊢[PRAAx] lt b D) : Γ ⊢[PRAAx]
    distanceBounded (finiteCoefficient a b N D) (limitCoefficient a b N) (derivativeCost (succ N)) D := by
  let A := D*a
  let C := numerator a b D
  let B := denominator b D
  let j := succ N
  have hb := le_trans h.andE₁ (le_of_lt h.andE₂)
  have hD := denominator_positive h hr
  have hBase := guard_rescale a b D h hD
  have hNext := neighbor_guard a b D h hr
  have rate := derivative_error A C B j one D hBase hNext hD (step_bound a b D hb hD)
  have sameCorrection := GaussianGammaNegativeCriticalRescale.correction_rescale a b N D h hD
  have sameNegative : Γ ⊢[PRAAx] qnegative (correction A B N) ≐ qnegative (correction a b N) :=
    GaussianInverseBinomialRows.negative_congr sameCorrection
  have target := (original_first_coefficient A B N hBase).eqTrans
    (qmul_congr (original_product_rescale a b D N h hD) sameNegative)
  exact distance_congr (.eqRefl _) target (by ipra_ring) (.eqRefl _) rate

theorem actual_original_negative_Gamma_unit_step_coefficients_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((guard (var 0) (var 1) ⋏ lt (var 1) (var 3)) ⟶
        (qsub (neighborProduct (var 0) (var 1) (var 2) (var 3)) (product (var 0) (var 1) (var 2)) ≐
          qmul (ofGaussian oneCode (var 3)) (finiteCoefficient (var 0) (var 1) (var 2) (var 3))) ⋏
        distanceBounded (finiteCoefficient (var 0) (var 1) (var 2) (var 3)) (limitCoefficient (var 0) (var 1) (var 2))
          (derivativeCost (succ (var 2))) (var 3)) :=
  closeUniv 4 (.impI (.andI
    (exact_product_step _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)
    (finite_coefficient_rate _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂)))

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeIntervalStepCoefficient
