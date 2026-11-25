import IPRADerivations.Analysis.GaussianStirlingDuplicationAlgebra

/-!
# Exact rational algebra of the Stirling half step

The doubled Gamma logarithm identity and the split logarithm of the
argument reduce the Stirling difference to half the Wallis logarithm
and the signed duplication residual.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingHalfStepAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale)
open GaussianRationalHorner (qadd qmul qadd_canonical qadd_represents qmul_represents represents
  canonical_unique represents_congr represents_rescale ofGaussian_represents positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (qsub qsub_canonical qsub_represents)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRootAlgebra (sub equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_scale im_scale
  re_one im_one)
open GaussianStirlingDifferenceAlgebra (rawA)
open GaussianStirlingDuplicationAlgebra (rawResidual)
open GaussianStirlingGammaLogarithm (arg)
open GaussianStirlingNames (point offset)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rawHalfGamma (g l h : PTm n) : PTm n :=
  qmul (point one two) (qadd h (qadd l (qadd g g)))

set_option maxHeartbeats 1800000 in
theorem half_step_value (N g l w h : PTm n) :
    Γ ⊢[PRAAx] qsub (rawA (two*N+one) two (rawHalfGamma g l h) (qadd l w)) (rawA N one g l)
      ≐ qadd (qmul (point one two) h) (rawResidual N one w) := by
  let D := rawDen g*rawDen l*rawDen w*rawDen h
  let T := two*D
  let G := scale (rawDen l*rawDen w*rawDen h) (rawGaussian g)
  let L := scale (rawDen g*rawDen w*rawDen h) (rawGaussian l)
  let W := scale (rawDen g*rawDen l*rawDen h) (rawGaussian w)
  let H := scale (rawDen g*rawDen l*rawDen w) (rawGaussian h)
  have h₂ : Γ ⊢[PRAAx] le one (two : PTm n) := le_succ_self one
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _
    (positive_product _ _ (positive_product _ _ (raw_den_positive g) (raw_den_positive l))
      (raw_den_positive w)) (raw_den_positive h)
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ h₂ hD
  have rg : Γ ⊢[PRAAx] represents g G D := rescale_to _ _ _ _ _ (raw_represents g) (by unfold D; ipra_ring)
  have rl : Γ ⊢[PRAAx] represents l L D := rescale_to _ _ _ _ _ (raw_represents l) (by unfold D; ipra_ring)
  have rw : Γ ⊢[PRAAx] represents w W D := rescale_to _ _ _ _ _ (raw_represents w) (by unfold D; ipra_ring)
  have rh : Γ ⊢[PRAAx] represents h H D := rescale_to _ _ _ _ _ (raw_represents h) (by unfold D; ipra_ring)
  have px : Γ ⊢[PRAAx] represents (point N one) (scale two (arg N)) two :=
    rescale_to _ _ one two two (ofGaussian_represents (arg N) one (le_refl one)) (one_mul two)
  have py := ofGaussian_represents (arg (two*N+one)) two h₂
  have ph := ofGaussian_represents (arg one) two h₂
  have ox : Γ ⊢[PRAAx] represents (offset N one) _ two := qsub_represents _ _ _ _ _ h₂ px ph
  have oy : Γ ⊢[PRAAx] represents (offset (two*N+one) two) _ two := qsub_represents _ _ _ _ _ h₂ py ph
  have gl := qmul_represents _ _ _ _ two D h₂ hD ph
    (qadd_represents _ _ _ _ D hD rh
      (qadd_represents _ _ _ _ D hD rl (qadd_represents _ _ _ _ D hD rg rg)))
  have left := qadd_represents _ _ _ _ T hT
    (qsub_represents _ _ _ _ T hT gl
      (qmul_represents _ _ _ _ two D h₂ hD oy (qadd_represents _ _ _ _ D hD rl rw)))
    (represents_rescale _ _ two D py)
  have right := qadd_represents _ _ _ _ T hT
    (qsub_represents _ _ _ _ T hT (rescale_to _ _ D two T rg (mul_comm _ _))
      (qmul_represents _ _ _ _ two D h₂ hD ox rl))
    (represents_rescale _ _ two D px)
  have lhs := qsub_represents _ _ _ _ T hT left right
  have rhs := qadd_represents _ _ _ _ T hT (qmul_represents _ _ _ _ two D h₂ hD ph rh)
    (qsub_represents _ _ _ _ T hT (represents_rescale _ _ two D ph)
      (qmul_represents _ _ _ _ two D h₂ hD px rw))
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (qadd_canonical _ _) hT (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;>
    simp only [arg,re_add,im_add,re_sub,im_sub,re_scale,im_scale,re_mul,im_mul,re_one,im_one] <;> ipra_simps <;> ring

end LeanProofs.IPRA.Analysis.GaussianStirlingHalfStepAlgebra
