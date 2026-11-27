import IPRADerivations.Analysis.Stirling.GammaLogarithm.GaussianStirlingNames
import IPRADerivations.Analysis.Stirling.Telescoping.Differences.GaussianStirlingDifference
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumAlgebra

/-!
# Exact rational algebra of the Stirling difference

The logarithm values may be arbitrary codes at this stage. All
expressions use the original rational coefficients. Clearing the
denominators checks the cancellation in both Gaussian components.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingDifferenceAlgebra

open_ipra
open ComplexLogarithmRemainder (scale oneCode)
open GaussianRationalHorner (qadd qmul represents qadd_represents qmul_represents qadd_canonical
  canonical_unique represents_congr represents_rescale ofGaussian_represents positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (qsub qsub_canonical qsub_represents)
open GaussianRationalSyntheticDivision (qone rescale_to)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_sub im_sub re_mul im_mul re_scale im_scale re_one im_one sub)
open GaussianStirlingGammaLogarithm (source arg)
open GaussianStirlingNames (point offset)
open GaussianStirlingDifference (coefficient)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rawA (a b g l : PTm n) : PTm n := qadd (qsub g (qmul (offset a b) l)) (point a b)
def rawDifference (a b t : PTm n) : PTm n := qsub (qmul (coefficient a b) t) qone

ipra_subst rawA

ipra_subst rawDifference [GaussianStirlingDifference.subst_coefficient]

private theorem point_rep (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] represents (point a b) (scale two (arg a)) (two*b) :=
  rescale_to _ _ b two (two*b) (ofGaussian_represents (arg a) b hb) (mul_comm _ _)

private theorem offset_rep (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] represents (offset a b) (sub (scale two (arg a)) (scale b (arg one))) (two*b) :=
  qsub_represents _ _ _ _ _ (positive_product _ _ (le_succ_self one) hb) (point_rep a b hb)
    (represents_rescale _ _ two b (ofGaussian_represents (arg one) two (le_succ_self one)))

theorem shifted_offset (a b : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] offset (a+b) b ≐ coefficient a b := by
  have hB : Γ ⊢[PRAAx] le one (two*b) := positive_product _ _ (le_succ_self one) hb
  have rep := offset_rep (a+b) b hb
  have nEq : Γ ⊢[PRAAx] equal (sub (scale two (arg (a+b))) (scale b (arg one))) (arg (two*a+b)) := by
    apply equal_of_values <;> simp only [arg,re_sub,im_sub,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  exact GaussianRationalHorner.cleared_input_exact _ _ _ (qsub_canonical _ _) hB
    (represents_congr (.eqRefl _) nEq (.eqRefl _) rep)

set_option maxHeartbeats 1800000 in
theorem difference_value (a b g l t : PTm n) (hb : Γ ⊢[PRAAx] le one b) :
    Γ ⊢[PRAAx] qsub (rawA a b g l) (rawA (a+b) b (qadd l g) (qadd l t)) ≐ rawDifference a b t := by
  let C := two*b
  let D := rawDen g*rawDen l*rawDen t
  let T := C*D
  let G := scale (rawDen l*rawDen t) (rawGaussian g)
  let L := scale (rawDen g*rawDen t) (rawGaussian l)
  let V := scale (rawDen g*rawDen l) (rawGaussian t)
  let ca := sub (scale two (arg a)) (scale b (arg one))
  let cb := sub (scale two (arg (a+b))) (scale b (arg one))
  let cp := arg (two*a+b)
  have hC : Γ ⊢[PRAAx] le one C := positive_product _ _ (le_succ_self one) hb
  have hD : Γ ⊢[PRAAx] le one D := positive_product _ _
    (positive_product _ _ (raw_den_positive g) (raw_den_positive l)) (raw_den_positive t)
  have hT : Γ ⊢[PRAAx] le one T := positive_product _ _ hC hD
  have rg : Γ ⊢[PRAAx] represents g G D := rescale_to _ _ _ _ _ (raw_represents g) (by unfold D; ipra_ring)
  have rl : Γ ⊢[PRAAx] represents l L D := rescale_to _ _ _ _ _ (raw_represents l) (by unfold D; ipra_ring)
  have rt : Γ ⊢[PRAAx] represents t V D := rescale_to _ _ _ _ _ (raw_represents t) (by unfold D; ipra_ring)
  have lg := qadd_represents l g L G D hD rl rg
  have lt' := qadd_represents l t L V D hD rl rt
  have ax := represents_rescale _ _ C D (point_rep a b hb)
  have bx := represents_rescale _ _ C D (point_rep (a+b) b hb)
  have gg := rescale_to g G D C T rg (mul_comm _ _)
  have ll := rescale_to (qadd l g) _ D C T lg (mul_comm _ _)
  have qa := qmul_represents (offset a b) l ca L C D hC hD (offset_rep a b hb) rl
  have qb := qmul_represents (offset (a+b) b) (qadd l t) cb _ C D hC hD (offset_rep (a+b) b hb) lt'
  have qd := qmul_represents (coefficient a b) t cp V C D hC hD (ofGaussian_represents _ _ hC) rt
  have left := qadd_represents _ _ _ _ T hT (qsub_represents _ _ _ _ T hT gg qa) ax
  have right := qadd_represents _ _ _ _ T hT (qsub_represents _ _ _ _ T hT ll qb) bx
  have lhs := qsub_represents _ _ _ _ T hT left right
  have rhs := qsub_represents _ _ _ _ T hT qd (GaussianRationalReciprocal.qone_represents_scaled T)
  apply canonical_unique _ _ _ _ (qsub_canonical _ _) (qsub_canonical _ _) hT (hrv := rhs)
  apply represents_congr (.eqRefl _) (hAB := .eqRefl _) (h := lhs)
  apply equal_of_values <;>
    simp only [ca,cb,cp,arg,T,C,re_add,im_add,re_sub,im_sub,re_scale,im_scale,re_mul,im_mul,re_one,im_one] <;>
    ipra_simps <;> ring

end LeanProofs.IPRA.Analysis.GaussianStirlingDifferenceAlgebra
