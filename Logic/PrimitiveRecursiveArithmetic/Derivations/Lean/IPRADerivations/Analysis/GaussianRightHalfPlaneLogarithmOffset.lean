import IPRADerivations.Analysis.GaussianRightHalfPlaneLogarithmLocalBound
import IPRADerivations.Analysis.GaussianLogGammaEulerHead
import IPRADerivations.Analysis.GaussianLocalLogarithmName
import IPRADerivations.Analysis.GaussianFiniteLogarithmCompositionTail

/-!
# Native one-eighth offsets for the canonical logarithm

The literal difference from one provides the Mercator input. Its native
disk certificate supplies both coordinate bounds for the canonical name
and the original Mercator source. Adding the exact rational one to this
same offset gives the Euler head's original signed point.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmOffset

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (code re im add scale oneCode eval_re_code eval_im_code)
open GaussianFiniteLogarithmCompositionTail (linearValue)
open LeanProofs.IPRA.Foundations.GapDecision (zabs zabs_congr zabs_neg)
open GaussianL1 (abs_ofNat)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents qadd_canonical
  qadd_represents canonical_unique represents_congr)
open GaussianRationalReciprocal (qone qone_represents_scaled)
open GaussianRootAlgebra (equal equal_of_values re_add im_add re_scale im_scale re_one im_one)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open RationalArithmetic (select select_zero select_one)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "ad" => LeanProofs.IPRA.Probability.Variance.ad

def signedImag (B neg : PTm n) : ZT n := ⟨select neg B zero, select neg zero B⟩
def offset (A B D neg : PTm n) : PTm n := code (ZT.ofNat A-ZT.ofNat D) (signedImag B neg)
def source (A B D neg R : PTm n) : Fm PTm n :=
  GaussianRightHalfPlaneLogarithm.source A D neg ⋏
    (ComplexLogarithmRemainder.bounded (offset A B D neg) R ⋏ le (num 8*R) D)

@[simp] theorem subst_signedImag {m : ℕ} (σ : Fin n → PTm m) (B neg : PTm n) :
    (signedImag B neg).subst σ = signedImag (Syn.subst σ B) (Syn.subst σ neg) := by
  simp [signedImag,ZT.subst]

@[simp] theorem subst_offset {m : ℕ} (σ : Fin n → PTm m) (A B D neg : PTm n) :
    Syn.subst σ (offset A B D neg) = offset (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) := by
  simp [offset]

@[simp] theorem subst_source {m : ℕ} (σ : Fin n → PTm m) (A B D neg R : PTm n) :
    (source A B D neg R).subst σ =
      source (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ D) (Syn.subst σ neg) (Syn.subst σ R) := by
  simp [source,GaussianRightHalfPlaneLogarithm.source,ComplexLogarithmRemainder.bounded]

private theorem absolute_real (A B D neg : PTm n) :
    Γ ⊢[PRAAx] zabs (re (offset A B D neg)) ≐ ad A D := by
  apply zabs_congr (v := ⟨A,D⟩)
  unfold offset
  rw [eval_re_code,ZT.toZ_sub,ZT.toZ_ofNat,ZT.toZ_ofNat]
  rfl

private theorem absolute_imaginary (A B D neg : PTm n) (h : Γ ⊢[PRAAx] neg ≐ zero ⋎ neg ≐ one) :
    Γ ⊢[PRAAx] zabs (im (offset A B D neg)) ≐ B := by
  refine .orE h ?_ ?_
  · let Δ := (neg ≐ zero) :: Γ
    have u := natEq (select_zero (Γ := Δ) neg B zero Prf.hyp0)
    have v := natEq (select_zero (Γ := Δ) neg zero B Prf.hyp0)
    have e : Δ ⊢[PRAAx] zabs (im (offset A B D neg)) ≐ zabs (ZT.ofNat B) := by
      apply zabs_congr
      unfold offset
      rw [eval_im_code,ZT.toZ_ofNat]
      simp only [signedImag,ZT.toZ]
      rw [u,v]
      ipra_simps
      ring
    exact e.eqTrans (abs_ofNat B)
  · let Δ := (neg ≐ one) :: Γ
    have u := natEq (select_one (Γ := Δ) neg B zero Prf.hyp0)
    have v := natEq (select_one (Γ := Δ) neg zero B Prf.hyp0)
    have e : Δ ⊢[PRAAx] zabs (im (offset A B D neg)) ≐ zabs (-(ZT.ofNat B)) := by
      apply zabs_congr
      unfold offset
      rw [eval_im_code,ZT.toZ_neg,ZT.toZ_ofNat]
      simp only [signedImag,ZT.toZ]
      rw [u,v]
      ipra_simps
      ring
    exact e.eqTrans ((zabs_neg _).eqTrans (abs_ofNat B))

theorem offset_coordinate_bounds (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] le (ad A D) R ⋏ le B R := by
  let z := offset A B D neg
  have sq : Γ ⊢[PRAAx] le ((one*one)*ComplexLogarithmRemainder.normSq z) ((R*R)*(one*one)) :=
    le_congr (by ipra_ring) (by ipra_ring) h.andE₂.andE₁
  have both := GaussianCoordinateRadius.native_coordinates z R one one sq
  have er : Γ ⊢[PRAAx] one*zabs (re z) ≐ ad A D := (one_mul _).eqTrans (absolute_real A B D neg)
  have ei : Γ ⊢[PRAAx] one*zabs (im z) ≐ B :=
    (one_mul _).eqTrans (absolute_imaginary A B D neg h.andE₁.andE₁.andE₂)
  exact .andI (le_congr er (by ipra_ring) both.andE₁) (le_congr ei (by ipra_ring) both.andE₂)

theorem box (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithmLocalBound.box A B D := by
  have coord := offset_coordinate_bounds A B D neg R h
  have width := h.andE₂.andE₂
  have known : Γ ⊢[PRAAx] le (num 8*ad A D) D :=
    le_trans (le_mul_mono (le_refl _) coord.andE₁) width
  have forward := Probability.MedianWeighted.le_add_ad (Γ := Γ) A D
  have back := Probability.MedianWeighted.le_add_ad (Γ := Γ) D A
  have comm : Γ ⊢[PRAAx] ad D A ≐ ad A D := by unfold Probability.Variance.ad; exact add_comm _ _
  have reverse := le_congr (.eqRefl _) (congrAdd (.eqRefl A) comm) back
  have lower : Γ ⊢[PRAAx] le (num 7*D) (num 8*A) := by ipra_le 8*sl reverse+sl known
  have upper : Γ ⊢[PRAAx] le (num 8*A) (num 9*D) := by ipra_le 8*sl forward+sl known
  have imag : Γ ⊢[PRAAx] le (num 8*B) D := le_trans (le_mul_mono (le_refl _) coord.andE₂) width
  exact .andI h.andE₁.andE₁.andE₁ (.andI h.andE₁.andE₂ (.andI lower (.andI upper imag)))

theorem local_source (A B D neg R : PTm n) (h : Γ ⊢[PRAAx] source A B D neg R) :
    Γ ⊢[PRAAx] GaussianLocalLogarithmName.source (offset A B D neg) R D := by
  have shrink : Γ ⊢[PRAAx] le (two*R) (num 8*R) := by ipra_le 6*𝔞 R
  exact .andI h.andE₁.andE₂ (.andI h.andE₂.andE₁ (le_trans shrink h.andE₂.andE₂))

theorem linear_value (A B D neg : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] linearValue (ofGaussian (offset A B D neg) D) ≐ GaussianLogGammaEulerHead.argument A B D neg := by
  let w := offset A B D neg
  let z := code (ZT.ofNat A) (signedImag B neg)
  let Q := scale D oneCode
  let l := linearValue (ofGaussian w D)
  let r := GaussianLogGammaEulerHead.argument A B D neg
  have e : Γ ⊢[PRAAx] equal (add Q w) z := by
    apply equal_of_values <;>
      simp only [Q,w,z,offset,re_add,im_add,re_scale,im_scale,re_one,im_one,eval_re_code,eval_im_code,ZT.toZ_ofNat,ZT.toZ_sub] <;>
      ring
  have sum := qadd_represents qone (ofGaussian w D) Q w D hD
    (qone_represents_scaled D) (ofGaussian_represents w D hD)
  exact canonical_unique l r z D (qadd_canonical _ _) (ofGaussian_canonical z D hD) hD
    (represents_congr (.eqRefl _) e (.eqRefl _) sum) (ofGaussian_represents z D hD)

theorem actual_right_half_plane_centered_offset_admission_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (source (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        (GaussianRightHalfPlaneLogarithmLocalBound.box (var 0) (var 1) (var 2) ⋏
          (GaussianLocalLogarithmName.source (offset (var 0) (var 1) (var 2) (var 3)) (var 4) (var 2) ⋏
            (linearValue (ofGaussian (offset (var 0) (var 1) (var 2) (var 3)) (var 2)) ≐
              GaussianLogGammaEulerHead.argument (var 0) (var 1) (var 2) (var 3))))) :=
  closeUniv 5 (.impI (.andI (box _ _ _ _ _ Prf.hyp0)
    (.andI (local_source _ _ _ _ _ Prf.hyp0) (linear_value _ _ _ _ Prf.hyp0.andE₁.andE₂))))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmOffset
