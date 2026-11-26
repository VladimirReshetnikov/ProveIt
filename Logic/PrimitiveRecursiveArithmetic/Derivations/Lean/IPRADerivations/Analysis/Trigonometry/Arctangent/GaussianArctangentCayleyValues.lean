import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalReciprocal

/-!
# Exact Gaussian rational Cayley values on the arctangent grid

The literal rational code is ((M+ij)/(M-ij)), written with a positive
integer denominator. Its norm is one, and its two endpoints at
(j=0,M) are exactly one and the positive imaginary unit.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianArctangentCayleyValues

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (code scale oneCode normSq normSq_eval eval_re_code eval_im_code)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents represents
  represents_rescale represents_congr canonical_unique positive_product)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRootAlgebra (equal equal_of_values equal_refl re_scale im_scale re_one im_one)
open GaussianRationalMetric (bounded bounded_of_cleared)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def numerator (M j : PTm n) : PTm n :=
  code (ZT.ofNat (M*M)-ZT.ofNat (j*j)) (ZT.ofNat (two*M*j))

def denominator (M j : PTm n) : PTm n := M*M+j*j
def value (M j : PTm n) : PTm n := ofGaussian (numerator M j) (denominator M j)
def imaginaryCode : PTm n := code (ZT.ofNat zero) (ZT.ofNat one)
def imaginaryPoint : PTm n := ofGaussian imaginaryCode one

theorem denominator_positive (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] le one (denominator M j) :=
  le_trans (positive_product M M hM hM) (le_add_right _ _)

theorem exact_square_norm (M j : PTm n) : Γ ⊢[PRAAx]
    normSq (numerator M j) ≐ denominator M j*denominator M j := by
  apply deriveNat
  rw [normSq_eval]
  simp only [numerator,denominator,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat]
  ipra_simps
  ring

theorem unit_bound (M j : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] bounded (value M j) one one := by
  let A := numerator M j
  let D := denominator M j
  have hD := denominator_positive M j hM
  apply bounded_of_cleared _ A D one one hD (le_refl _) (ofGaussian_represents _ _ hD)
  exact le_congr (by ipra_ring) (by ipra_ring) (le_congr (exact_square_norm M j).eqSymm (.eqRefl _) (le_refl (D*D)))

theorem left_endpoint (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] value M zero ≐ qone := by
  let d := denominator M zero
  have hd := denominator_positive M zero hM
  have e : Γ ⊢[PRAAx] equal (numerator M zero) (scale d oneCode) := by
    dsimp only [d]
    apply equal_of_values <;>
      simp only [numerator,denominator,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat,re_scale,im_scale,re_one,im_one] <;>
      ipra_simps <;> ring
  exact canonical_unique _ _ _ d (ofGaussian_canonical _ _ hd) (ofGaussian_canonical _ _ (le_refl one)) hd
    (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ hd)) (qone_represents_scaled d)

theorem right_endpoint (M : PTm n) (hM : Γ ⊢[PRAAx] le one M) :
    Γ ⊢[PRAAx] value M M ≐ (imaginaryPoint : PTm n) := by
  let d := denominator M M
  have hd := denominator_positive M M hM
  have e : Γ ⊢[PRAAx] equal (numerator M M) (scale d imaginaryCode) := by
    dsimp only [d]
    apply equal_of_values <;>
      simp only [numerator,denominator,imaginaryCode,eval_re_code,eval_im_code,ZT.toZ_sub,ZT.toZ_ofNat,re_scale,im_scale] <;>
      ipra_simps <;> ring
  have rep : Γ ⊢[PRAAx] represents (imaginaryPoint : PTm n) (scale d imaginaryCode) d :=
    represents_congr (.eqRefl _) (equal_refl _) (one_mul d)
      (represents_rescale _ imaginaryCode one d (ofGaussian_represents _ _ (le_refl one)))
  exact canonical_unique _ _ _ d (ofGaussian_canonical _ _ hd) (ofGaussian_canonical _ _ (le_refl one)) hd
    (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ hd)) rep

theorem actual_original_Cayley_arctangent_grid_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
    (le one (var 0) ⟶
      ((bounded (value (var 0) (var 1)) one one ⋏ (value (var 0) zero ≐ qone)) ⋏
        value (var 0) (var 0) ≐ imaginaryPoint)) :=
  closeUniv 2 (.impI (.andI (.andI (unit_bound _ _ Prf.hyp0) (left_endpoint _ Prf.hyp0))
    (right_endpoint _ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianArctangentCayleyValues
