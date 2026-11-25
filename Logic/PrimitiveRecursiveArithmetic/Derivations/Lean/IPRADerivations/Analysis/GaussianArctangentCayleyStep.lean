import IPRADerivations.Analysis.GaussianArctangentCayleyValues

/-!
# Exact local defect of the conjugate Cayley grid

Multiplying the next conjugate grid value by the linear exponential
factor gives the current value up to an explicit rational defect of
norm at most (2/M²). This is the local step for the finite arctangent
exponential telescope.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleyStep

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianArctangentCayleyValues (numerator denominator denominator_positive)
open ComplexLogarithmRemainder (code scale oneCode add mul normSq normSq_eval eval_re_code eval_im_code)
open GaussianRationalHorner (qadd qmul ofGaussian ofGaussian_canonical ofGaussian_represents canonical_unique
  qadd_canonical qadd_represents qmul_represents represents_congr represents_rescale positive_product)
open GaussianRationalReciprocal (qone qone_represents_scaled conjugate re_conjugate im_conjugate)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub qsub_represents)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_add im_add re_mul im_mul re_sub im_sub re_scale im_scale re_one im_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (succ zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def conjugateValue (M j : PTm n) : PTm n := ofGaussian (conjugate (numerator M j)) (denominator M j)
def incrementCode (M : PTm n) : PTm n := code (ZT.ofNat zero) (ZT.ofNat (two*M))
def increment (M j : PTm n) : PTm n := ofGaussian (incrementCode M) (denominator M j)
def linearCode (M j : PTm n) : PTm n := code (ZT.ofNat (denominator M j)) (ZT.ofNat (two*M))
def defectCode (M j : PTm n) : PTm n :=
  code (ZT.ofNat (two*(M*M))) (-(ZT.ofNat (two*M*succ j)))

private theorem linear_representation (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] GaussianRationalHorner.represents (qadd qone (increment M j)) (linearCode M j) (denominator M j) := by
  let d := denominator M j
  have hd := denominator_positive M j hM
  have rep := qadd_represents qone (increment M j) (scale d oneCode) (incrementCode M) d hd
    (qone_represents_scaled d) (ofGaussian_represents _ _ hd)
  apply represents_congr (.eqRefl _) ?_ (.eqRefl _) rep
  apply equal_of_values <;>
    simp only [linearCode,incrementCode,re_add,im_add,re_scale,im_scale,re_one,im_one,eval_re_code,eval_im_code,ZT.toZ_ofNat] <;>
    dsimp only [d] <;> ipra_simps <;> ring

theorem linear_value (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] qadd qone (increment M j) ≐ ofGaussian (linearCode M j) (denominator M j) :=
  canonical_unique _ _ _ _ (qadd_canonical _ _) (ofGaussian_canonical _ _ (denominator_positive M j hM))
    (denominator_positive M j hM) (linear_representation M j hM) (ofGaussian_represents _ _ (denominator_positive M j hM))

private theorem defect_native (M j : PTm n) : Γ ⊢[PRAAx] equal
    (GaussianRootAlgebra.sub (mul (linearCode M j) (conjugate (numerator M (succ j))))
      (scale (denominator M (succ j)) (conjugate (numerator M j)))) (defectCode M j) := by
  apply equal_of_values <;>
    simp only [re_sub,im_sub,re_mul,im_mul,re_scale,im_scale,re_conjugate,im_conjugate,
      linearCode,numerator,defectCode,denominator,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat,ZT.toZ_neg] <;>
    ipra_simps <;> ring

theorem defect_representation (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] GaussianRationalHorner.represents
      (qsub (qmul (qadd qone (increment M j)) (conjugateValue M (succ j))) (conjugateValue M j))
      (defectCode M j) (denominator M j*denominator M (succ j)) := by
  let d := denominator M j
  let e := denominator M (succ j)
  have hd := denominator_positive M j hM
  have he := denominator_positive M (succ j) hM
  have hde := positive_product d e hd he
  have product := qmul_represents (qadd qone (increment M j)) (conjugateValue M (succ j))
    (linearCode M j) (conjugate (numerator M (succ j))) d e hd he (linear_representation M j hM)
    (ofGaussian_represents _ _ he)
  have lifted := represents_rescale (conjugateValue M j) (conjugate (numerator M j)) d e (ofGaussian_represents _ _ hd)
  have difference := qsub_represents _ _ _ _ _ hde product lifted
  exact represents_congr (.eqRefl _) (defect_native M j) (.eqRefl _) difference

theorem local_defect (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] distanceBounded (qmul (qadd qone (increment M j)) (conjugateValue M (succ j)))
      (conjugateValue M j) two (M*M) := by
  let d := denominator M j
  let e := denominator M (succ j)
  have hd := denominator_positive M j hM
  have he := denominator_positive M (succ j) hM
  have hde := positive_product d e hd he
  have hh := positive_product M M hM hM
  have norm : Γ ⊢[PRAAx] normSq (defectCode M j) ≐ (two*two)*(M*M)*e := by
    apply deriveNat
    rw [normSq_eval]
    simp only [defectCode,e,denominator,eval_re_code,eval_im_code,ZT.toZ_ofNat,ZT.toZ_neg]
    ipra_simps
    ring
  have db : Γ ⊢[PRAAx] le (M*M) d := le_add_right _ _
  have eb : Γ ⊢[PRAAx] le (M*M) e := le_add_right _ _
  have bound := le_mul_mono (le_refl ((two*two)*e)) (le_mul_mono (le_mul_mono db db) eb)
  have left : Γ ⊢[PRAAx] ((M*M)*(M*M))*normSq (defectCode M j) ≐
      (two*two)*e*((M*M)*(M*M)*(M*M)) :=
    (congrMul (.eqRefl _) norm).eqTrans (by ipra_ring)
  apply bounded_of_cleared _ _ (d*e) two (M*M) hde hh (defect_representation M j hM)
  exact le_congr left.eqSymm (by ipra_ring) bound

theorem actual_original_arctangent_Cayley_step_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶ distanceBounded
      (qmul (qadd qone (increment (var 0) (var 1))) (conjugateValue (var 0) (succ (var 1))))
      (conjugateValue (var 0) (var 1)) two (var 0*var 0)) :=
  closeUniv 2 (.impI (local_defect _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleyStep
