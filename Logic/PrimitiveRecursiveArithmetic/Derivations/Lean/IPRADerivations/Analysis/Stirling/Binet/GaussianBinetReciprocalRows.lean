import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerChartAgreement
import IPRADerivations.Analysis.Gamma.EulerProducts.GaussianLogGammaEulerLinearSlope
import IPRADerivations.Analysis.RationalArithmetic.GaussianRationalLowerBounds

/-!
# The sharp reciprocal rectangle bound for the complex digamma estimate

On a horizontal unit interval in the right half-plane, the distance
from the reciprocal at the left endpoint to any tagged reciprocal is
bounded by the corresponding difference of positive real reciprocals.
The bound uses the actual normalized rational reciprocal and applies
at every internal mesh size, including both endpoint tags.
-/

set_option autoImplicit false
set_option maxHeartbeats 260000

namespace LeanProofs.IPRA.Analysis.GaussianBinetReciprocalRows

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (eval_re_code eval_im_code normSq normSq_one normSq_scale oneCode scale)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerReciprocalSlope (shiftedPoint)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianRationalHorner (ofGaussian_represents positive_product qmul)
open GaussianRationalLowerBounds (lower lower_from_representation inverse_bound name_lower)
open GaussianRationalMetric (bounded bounded_of_cleared distanceBounded qsub qsub_represents)
open GaussianRationalReciprocal (reciprocal bound_congr bounded_product)
open GaussianRightHalfPlaneLogarithm (source)
open GaussianRootAlgebra (equal equal_of_values im_one im_scale im_sub normSq_equal re_one re_scale re_sub sub)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

theorem real_part_lower (A B D neg : PTm n) (h : Γ ⊢[PRAAx] source A D neg) :
    Γ ⊢[PRAAx] lower (argument A B D neg) A D := by
  have hd := h.andE₂
  have hn := native_norm A B neg h.andE₁.andE₂
  apply lower_from_representation _ (native A B neg) D A D hd hd (ofGaussian_represents _ _ hd)
  have hi : Γ ⊢[PRAAx] le (A*A*(D*D)) (D*D*(A*A+B*B)) := by ipra_le 𝔞(D*D)*𝔞(B*B)
  exact le_congr (.eqRefl _) (congrMul (.eqRefl _) hn.eqSymm) hi

theorem same_imaginary_shift (A U B neg : PTm n) : Γ ⊢[PRAAx]
    equal (sub (native (A+U) B neg) (native A B neg)) (scale U oneCode) := by
  apply equal_of_values
  · simp only [re_sub, re_scale, re_one, native, eval_re_code, ZT.toZ_ofNat]
    ipra_simps
    ring
  · simp only [im_sub, im_scale, im_one, native, eval_im_code]
    ring

theorem horizontal_step (A B D neg U : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    distanceBounded (argument (A+U) B D neg) (argument A B D neg) U D := by
  let x := native (A+U) B neg
  let y := native A B neg
  have diff := qsub_represents _ _ x y D hD (ofGaussian_represents _ _ hD) (ofGaussian_represents _ _ hD)
  have norm : Γ ⊢[PRAAx] normSq (sub x y) ≐ U*U := (normSq_equal (same_imaginary_shift (Γ := Γ) A U B neg)).eqTrans
    ((normSq_scale U oneCode).eqTrans ((congrMul (.eqRefl _) normSq_one).eqTrans (by ipra_ring)))
  exact bounded_of_cleared _ (sub x y) D U D hD hD diff
    (le_congr (congrMul (.eqRefl _) norm.eqSymm) (.eqRefl _) (by ipra_le 0))

theorem horizontal_reciprocal_distance (A B D neg U : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    distanceBounded (reciprocal (argument A B D neg)) (reciprocal (argument (A+U) B D neg))
      (D*U) (A*(A+U)) := by
  let x := argument A B D neg
  let y := argument (A+U) B D neg
  have hA := h.andE₁.andE₁
  have hD := h.andE₂
  have hU := le_trans hA (le_add_right A U)
  have hx := real_part_lower A B D neg h
  have hy := real_part_lower (A+U) B D neg (.andI (.andI hU h.andE₁.andE₂) hD)
  have nx := GaussianNameReciprocal.lower_norm_positive x D hD (name_lower x A D hA hD hx)
  have ny := GaussianNameReciprocal.lower_norm_positive y D hD (name_lower y (A+U) D hU hD hy)
  have first := bounded_product (reciprocal x) (qsub y x) D A U D hA hD
    (inverse_bound x A D hA hD hx) (horizontal_step A B D neg U hD)
  have both := bounded_product (qmul (reciprocal x) (qsub y x)) (reciprocal y) (D*U) (A*D) D (A+U)
    (positive_product _ _ hA hD) hU first (inverse_bound y (A+U) D hU hD hy)
  have small := bounded_radius_mono _ _ _ (D*U) (A*(A+U))
    (positive_product _ _ (positive_product _ _ hA hD) hU) (positive_product _ _ hA hU) (by ipra_le 0) both
  exact bound_congr (GaussianNameReciprocal.inverse_difference x y nx ny).eqSymm (.eqRefl _) (.eqRefl _) small

def tagPoint (A B D neg k M j : PTm n) : PTm n :=
  argument (M*(A+k*D)+j*D) (M*B) (M*D) neg

@[simp] theorem subst_tagPoint {m : ℕ} (σ : Fin n → PTm m) (A B D neg k M j : PTm n) :
    Syn.subst σ (tagPoint A B D neg k M j) =
      tagPoint (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg)
        (Syn.subst σ k) (Syn.subst σ M) (Syn.subst σ j) := by simp [tagPoint]

theorem tag_distance (A B D neg k M j : PTm n) (h : Γ ⊢[PRAAx] source A D neg)
    (hM : Γ ⊢[PRAAx] le one M) (hj : Γ ⊢[PRAAx] le j M) : Γ ⊢[PRAAx]
    distanceBounded (reciprocal (shiftedPoint (argument A B D neg) k)) (reciprocal (tagPoint A B D neg k M j))
      (D*D) ((A+k*D)*(A+(k+one)*D)) := by
  let X := A+k*D
  let Y := M*X
  have hx := GaussianLogGammaEulerHead.shifted_source k A D neg h
  have hX := hx.andE₁.andE₁
  have hY := positive_product M X hM hX
  have hD := positive_product _ _ hM h.andE₂
  have hs : Γ ⊢[PRAAx] source Y (M*D) neg := .andI (.andI hY hx.andE₁.andE₂) hD
  have e := (GaussianLogGammaEulerLinearSlope.shifted_point A B D neg k h.andE₂).eqTrans
    (GaussianLogGammaEulerChartAgreement.scaled_argument X B D neg M (M*D) hx hM (.eqRefl _)).eqSymm
  have bound := horizontal_reciprocal_distance Y (M*B) (M*D) neg (j*D) hs
  have den := positive_product _ _ hX (le_trans h.andE₁.andE₁ (le_add_right A ((k+one)*D)))
  have narrowed := GaussianRationalDistanceOrder.distance_radius_mono _ _ _ _ (D*D) (X*(A+(k+one)*D))
    (positive_product _ _ hY (le_trans hY (le_add_right _ _))) den
    (by dsimp only [Y, X]; ipra_le 𝔞(D*D)*𝔞(A+k*D)^2*𝔞(M)*sl hj) bound
  exact GaussianRationalDistanceOrder.distance_congr
    (GaussianNameReciprocal.reciprocal_congr e).eqSymm (.eqRefl _) (.eqRefl _) (.eqRefl _) narrowed

theorem actual_complex_reciprocal_rectangle_tag_bound_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 7
    (source (var 0) (var 2) (var 3) ⟶ le one (var 5) ⟶ le (var 6) (var 5) ⟶
      distanceBounded (reciprocal (shiftedPoint (argument (var 0) (var 1) (var 2) (var 3)) (var 4)))
        (reciprocal (tagPoint (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6)))
        (var 2*var 2) ((var 0+var 4*var 2)*(var 0+(var 4+one)*var 2))) :=
  closeUniv 7 (.impI (.impI (.impI (tag_distance _ _ _ _ _ _ _ hyp2 Prf.hyp1 Prf.hyp0))))

end LeanProofs.IPRA.Analysis.GaussianBinetReciprocalRows
