import IPRADerivations.Analysis.Stirling.Telescoping.GaussianStirlingDifferenceAlgebra
import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingNativeDuplication

/-!
# Rational cancellation in the Stirling duplication formula

The Gamma increment is already replaced by the proved logarithmic law.
All six sampled logarithms share one denominator. Real coefficients
share a second denominator, so the final cancellation holds on both
Gaussian components at the product denominator.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingDuplicationAlgebra

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale oneCode neg)
open GaussianGaussMultiplicationPowerRate (multiplier)
open GaussianRationalHorner (qadd qmul represents represents_rescale ofGaussian_represents represents_congr
  qadd_represents qmul_represents canonical_unique qadd_canonical positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (qsub qnegative qsub_represents qnegative_represents qsub_canonical)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRootAlgebra (sub equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_scale im_scale
  re_one im_one re_neg im_neg equal_refl)
open GaussianStirlingDifferenceAlgebra (rawA)
open GaussianStirlingGammaLogarithm (arg)
open GaussianStirlingNames (point offset)
open GaussianStirlingNativeDuplication (halfNumerator halfDenominator)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "halfPoint" => point one two

def rawHalfGamma (a b g h j v : PTm n) : PTm n :=
  qsub (qadd (qadd (qmul (multiplier (arg a) b two) (qnegative v)) h) j) g
def rawResidual (a b w : PTm n) : PTm n := qsub halfPoint (qmul (point a b) w)
def rawConstant (h v : PTm n) : PTm n := qadd h (qmul halfPoint v)

private theorem point_rep (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] represents (point a b) (scale two (arg a)) (two*b) :=
  rescale_to _ _ b two (two*b) (ofGaussian_represents (arg a) b hb) (mul_comm _ _)

private theorem half_rep (b : PTm n) :
    Γ ⊢[PRAAx] represents (halfPoint : PTm n) (scale b (arg one)) (two*b) :=
  represents_rescale _ _ two b (ofGaussian_represents (arg one) two (le_succ_self one))

private theorem half_shift_rep (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] represents (point (halfNumerator a b) (halfDenominator b)) (arg (halfNumerator a b)) (two*b) :=
  represents_congr (.eqRefl _) (equal_refl _) (mul_comm b two)
    (ofGaussian_represents _ _ (positive_product b two hb (le_succ_self one)))

private theorem power_rep (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] represents (multiplier (arg a) b two)
      (sub (scale two (scale two (arg a))) (scale (two*b) oneCode)) (two*b) :=
  qsub_represents _ _ _ _ _ (positive_product _ _ (le_succ_self one) hb)
    (rescale_to _ _ b two (two*b) (ofGaussian_represents (scale two (arg a)) b hb) (mul_comm _ _))
    (GaussianRationalReciprocal.qone_represents_scaled (two*b))

set_option maxHeartbeats 2200000 in
theorem duplication_value (a b g h j u v w : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qsub
      (qadd (rawA a b g u) (rawA (halfNumerator a b) (halfDenominator b) (rawHalfGamma a b g h j v) (qadd u w)))
      (rawA (two*a) b j (qadd u v)) ≐ qadd (rawConstant h v) (rawResidual a b w) := by
  let C := two*b
  let D := rawDen g*(rawDen h*(rawDen j*(rawDen u*(rawDen v*rawDen w))))
  let T := C*D
  let G := scale (rawDen h*(rawDen j*(rawDen u*(rawDen v*rawDen w)))) (rawGaussian g)
  let H := scale (rawDen g*(rawDen j*(rawDen u*(rawDen v*rawDen w)))) (rawGaussian h)
  let J := scale (rawDen g*(rawDen h*(rawDen u*(rawDen v*rawDen w)))) (rawGaussian j)
  let U := scale (rawDen g*(rawDen h*(rawDen j*(rawDen v*rawDen w)))) (rawGaussian u)
  let V := scale (rawDen g*(rawDen h*(rawDen j*(rawDen u*rawDen w)))) (rawGaussian v)
  let W := scale (rawDen g*(rawDen h*(rawDen j*(rawDen u*rawDen v)))) (rawGaussian w)
  have hC : Γ ⊢[PRAAx] le one C := positive_product _ _ (le_succ_self one) hb
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _ (raw_den_positive g) (positive_product _ _ (raw_den_positive h)
    (positive_product _ _ (raw_den_positive j) (positive_product _ _ (raw_den_positive u)
      (positive_product _ _ (raw_den_positive v) (raw_den_positive w)))))
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ hC hD
  have rg : Γ ⊢[PRAAx] represents g G D := rescale_to _ _ _ _ _ (raw_represents g) (.eqRefl _)
  have rh : Γ ⊢[PRAAx] represents h H D := rescale_to _ _ _ _ _ (raw_represents h) (by unfold D; ipra_ring)
  have rj : Γ ⊢[PRAAx] represents j J D := rescale_to _ _ _ _ _ (raw_represents j) (by unfold D; ipra_ring)
  have ru : Γ ⊢[PRAAx] represents u U D := rescale_to _ _ _ _ _ (raw_represents u) (by unfold D; ipra_ring)
  have rv : Γ ⊢[PRAAx] represents v V D := rescale_to _ _ _ _ _ (raw_represents v) (by unfold D; ipra_ring)
  have rw' : Γ ⊢[PRAAx] represents w W D := rescale_to _ _ _ _ _ (raw_represents w) (by unfold D; ipra_ring)
  have gg := rescale_to g G D C T rg (mul_comm _ _)
  have hh := rescale_to h H D C T rh (mul_comm _ _)
  have jj := rescale_to j J D C T rj (mul_comm _ _)
  have uv := qadd_represents _ _ _ _ D hD ru rv
  have uw := qadd_represents _ _ _ _ D hD ru rw'
  have px := point_rep a b hb
  have ph := half_shift_rep a b hb
  have pd := point_rep (two*a) b hb
  have qh := half_rep (Γ := Γ) b
  have ox := qsub_represents _ _ _ _ C hC px qh
  have oh := qsub_represents _ _ _ _ C hC ph qh
  have od := qsub_represents _ _ _ _ C hC pd qh
  have pow := qmul_represents _ _ _ _ C D hC hD (power_rep a b hb) (qnegative_represents _ _ _ rv)
  have repl := qsub_represents _ _ _ _ T hT (qadd_represents _ _ _ _ T hT
    (qadd_represents _ _ _ _ T hT pow hh) jj) gg
  have left := qadd_represents _ _ _ _ T hT
    (qsub_represents _ _ _ _ T hT gg (qmul_represents _ _ _ _ C D hC hD ox ru))
    (represents_rescale _ _ C D px)
  have middle := qadd_represents _ _ _ _ T hT
    (qsub_represents _ _ _ _ T hT repl (qmul_represents _ _ _ _ C D hC hD oh uw))
    (represents_rescale _ _ C D ph)
  have right := qadd_represents _ _ _ _ T hT
    (qsub_represents _ _ _ _ T hT jj (qmul_represents _ _ _ _ C D hC hD od uv))
    (represents_rescale _ _ C D pd)
  have lhs := qsub_represents _ _ _ _ T hT (qadd_represents _ _ _ _ T hT left middle) right
  have rhs := qadd_represents _ _ _ _ T hT
    (qadd_represents _ _ _ _ T hT hh (qmul_represents _ _ _ _ C D hC hD qh rv))
    (qsub_represents _ _ _ _ T hT (represents_rescale _ _ C D qh) (qmul_represents _ _ _ _ C D hC hD px rw'))
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (qadd_canonical _ _) hT (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;>
    simp only [C,arg,halfNumerator,re_add,im_add,re_sub,im_sub,re_scale,im_scale,re_mul,im_mul,
      re_neg,im_neg,re_one,im_one] <;> ipra_simps <;> ring

end LeanProofs.IPRA.Analysis.GaussianStirlingDuplicationAlgebra
