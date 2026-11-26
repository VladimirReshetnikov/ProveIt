import IPRADerivations.Analysis.Stirling.Duplication.GaussianStirlingLogDuplication

/-!
# Exact rational coefficients of the Barnes duplication normalizer

At `z=A/(2B)`, the exponent of the normalizer is
`(-2z²+3z) log(1/2) - 2z log Gamma(1/2)`. At the half step
the first coefficient drops by the exact multiplier `2z-1` in the
original Gauss Gamma duplication factor, and the second drops by one.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationNormalizerCoefficients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (add scale oneCode)
open GaussianRootAlgebra (sub equal equal_of_values re_add im_add re_sub im_sub re_scale im_scale re_neg im_neg re_one im_one)
open GaussianRationalHorner (ofGaussian qadd qadd_represents qadd_canonical ofGaussian_represents ofGaussian_canonical
  positive_product represents represents_congr canonical_unique)
open GaussianRationalMetric (qsub qsub_represents)
open GaussianRationalReciprocal (qone_represents_scaled)
open GaussianRationalSyntheticDivision (qone rescale_to)
open GaussianGaussMultiplicationPowerRate (multiplier)
open GaussianStirlingGammaLogarithm (arg)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def quadraticNumerator (A B : PTm n) : PTm n := sub (scale (num 3*A*B) oneCode) (scale (A*A) oneCode)
def quadraticDenominator (B : PTm n) : PTm n := (two*B)*B
def quadraticWeight (A B : PTm n) : PTm n := ofGaussian (quadraticNumerator A B) (quadraticDenominator B)
def linearNumerator (A : PTm n) : PTm n := ComplexLogarithmRemainder.neg (scale A oneCode)
def linearWeight (A B : PTm n) : PTm n := ofGaussian (linearNumerator A) B

theorem quadratic_weight_step (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (quadraticWeight (A+B) B) (multiplier (arg A) (two*B) two) ≐ quadraticWeight A B := by
  let D := two*B
  let E := quadraticDenominator B
  let u := quadraticNumerator (A+B) B
  let v := quadraticNumerator A B
  let w := scale B (scale two (arg A))
  let t := scale E oneCode
  let g := multiplier (arg A) D two
  have hD : Γ ⊢[PRAAx] le one D := positive_product two B (le_succ_self one) hB
  have hE : Γ ⊢[PRAAx] le one E := positive_product D B hD hB
  have hq : Γ ⊢[PRAAx] represents (ofGaussian (scale two (arg A)) D) w E :=
    rescale_to _ _ D B E (ofGaussian_represents _ _ hD) (.eqRefl _)
  have hg : Γ ⊢[PRAAx] represents g (sub w t) E :=
    qsub_represents _ _ w t E hE hq (qone_represents_scaled E)
  have sum := qadd_represents (quadraticWeight (A+B) B) g u (sub w t) E hE (ofGaussian_represents _ _ hE) hg
  have nativeEq : Γ ⊢[PRAAx] equal (add u (sub w t)) v := by
    apply equal_of_values <;>
      simp only [u,v,w,t,E,quadraticNumerator,quadraticDenominator,arg,re_add,im_add,
        re_sub,im_sub,re_scale,im_scale,re_one,im_one] <;> ipra_simps <;> ring
  exact canonical_unique _ _ v E (qadd_canonical _ _) (ofGaussian_canonical _ _ hE) hE
    (represents_congr (.eqRefl _) nativeEq (.eqRefl _) sum) (ofGaussian_represents _ _ hE)

theorem linear_weight_step (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qadd (linearWeight (A+B) B) qone ≐ linearWeight A B := by
  let u := linearNumerator (A+B)
  let v := linearNumerator A
  let t := scale B oneCode
  have sum := qadd_represents (linearWeight (A+B) B) qone u t B hB (ofGaussian_represents _ _ hB)
    (qone_represents_scaled B)
  have nativeEq : Γ ⊢[PRAAx] equal (add u t) v := by
    apply equal_of_values <;>
      simp only [u,v,t,linearNumerator,re_add,im_add,re_neg,im_neg,re_scale,im_scale,re_one,im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ v B (qadd_canonical _ _) (ofGaussian_canonical _ _ hB) hB
    (represents_congr (.eqRefl _) nativeEq (.eqRefl _) sum) (ofGaussian_represents _ _ hB)

theorem actual_Barnes_duplication_normalizer_coefficients_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (let A := var 0; let B := var 1
       le one B ⟶
        ((qadd (quadraticWeight (A+B) B) (multiplier (arg A) (two*B) two) ≐ quadraticWeight A B) ⋏
         (qadd (linearWeight (A+B) B) qone ≐ linearWeight A B))) :=
  closeUniv 2 (.impI (.andI (quadratic_weight_step _ _ Prf.hyp0) (linear_weight_step _ _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalDuplicationNormalizerCoefficients
