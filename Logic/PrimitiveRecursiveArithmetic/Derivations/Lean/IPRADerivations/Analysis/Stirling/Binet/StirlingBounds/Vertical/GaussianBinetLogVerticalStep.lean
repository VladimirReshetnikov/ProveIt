import IPRADerivations.Analysis.Stirling.Binet.StirlingBounds.Logarithms.GaussianBinetLogHorizontalStep

/-!
# First-order logarithm comparison on a vertical Binet mesh

A vertical step keeps the real numerator fixed and changes the imaginary
magnitude by an arbitrary internal natural. The sign stays fixed. The
literal displacement supplies the linear term with the same error bound
as the general right-half-plane logarithm increment.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianBinetLogVerticalStep

open_ipra
open ComplexLogarithmRemainder (normSq eval_re_code eval_im_code)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerHead (argument)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianLogGammaEulerResidualRadius (native_norm)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner
  (canonical_unique ofGaussian ofGaussian_canonical ofGaussian_represents positive_product qmul represents_congr)
open GaussianRationalMetric (distanceBounded qsub qsub_canonical qsub_represents)
open GaussianRationalReciprocal (reciprocal)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianRightHalfPlaneLogarithm (source nameF data)
open GaussianRightHalfPlaneLogarithmIncrementMargin (admitted smallStep)
open GaussianRightHalfPlaneLogarithmOffset (signedImag)
open GaussianRightHalfPlaneLogarithmRelativeStep (relative relative_binding)
open GaussianRootAlgebra (equal equal_of_values re_sub im_sub normSq_equal sub)
open RationalArithmetic (select_zero select_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def step (H D neg : PTm n) : PTm n := ofGaussian (native zero H neg) D

ipra_subst step

private theorem signed_add (B H neg : PTm n) (hs : Γ ⊢[PRAAx] (neg ≐ zero) ⋎ (neg ≐ one)) :
    Γ ⊢[PRAAx] ZT.eq (signedImag (B+H) neg - signedImag B neg) (signedImag H neg) := by
  apply Prf.orE hs
  · let Δ := (neg ≐ zero) :: Γ
    have e (k l : PTm n) := natEq (select_zero (Γ := Δ) neg k l Prf.hyp0)
    refine ZT.derive (Γ := Δ) (u := signedImag (B+H) neg - signedImag B neg) (v := signedImag H neg) ?_
    rw [ZT.toZ_sub]
    simp only [signedImag,ZT.toZ,e]
    ipra_simps
    ring
  · let Δ := (neg ≐ one) :: Γ
    have e (k l : PTm n) := natEq (select_one (Γ := Δ) neg k l Prf.hyp0)
    refine ZT.derive (Γ := Δ) (u := signedImag (B+H) neg - signedImag B neg) (v := signedImag H neg) ?_
    rw [ZT.toZ_sub]
    simp only [signedImag,ZT.toZ,e]
    ipra_simps
    ring

theorem native_displacement (A B neg H : PTm n) (hs : Γ ⊢[PRAAx] (neg ≐ zero) ⋎ (neg ≐ one)) :
    Γ ⊢[PRAAx] equal (sub (native A (B+H) neg) (native A B neg)) (native zero H neg) := by
  apply equal_of_values
  · simp only [re_sub,native,eval_re_code,ZT.toZ_ofNat]
    ipra_simps
    ring
  · simpa only [native,im_sub,eval_im_code,ZT.toZ_sub] using ZT.toZ_eq (signed_add B H neg hs)

theorem native_step_bound (A B neg H : PTm n) (hs : Γ ⊢[PRAAx] (neg ≐ zero) ⋎ (neg ≐ one)) :
    Γ ⊢[PRAAx] ComplexLogarithmRemainder.bounded (sub (native A (B+H) neg) (native A B neg)) H := by
  have e := (normSq_equal (native_displacement A B neg H hs)).eqTrans
    ((native_norm zero H neg hs).eqTrans (show Γ ⊢[PRAAx] zero*zero+H*H ≐ H*H by ipra_ring))
  exact le_congr e.eqSymm (.eqRefl _) (le_refl _)

theorem relative_vertical (A B D neg H : PTm n) (h : Γ ⊢[PRAAx] source A D neg) : Γ ⊢[PRAAx]
    relative (native A B neg) (native A (B+H) neg) ≐ qmul (step H D neg) (reciprocal (argument A B D neg)) := by
  let u := native A B neg
  let v := native A (B+H) neg
  have hA := h.andE₁.andE₁
  have hd := h.andE₂
  have hs := h.andE₁.andE₂
  have hu : Γ ⊢[PRAAx] le one (normSq u) :=
    le_trans (positive_product A A hA hA)
      (le_congr (.eqRefl _) (native_norm A B neg hs).eqSymm (le_add_right (A*A) (B*B)))
  let w := qsub (ofGaussian v D) (ofGaussian u D)
  have rep := qsub_represents (ofGaussian v D) (ofGaussian u D) v u D hd
    (ofGaussian_represents _ _ hd) (ofGaussian_represents _ _ hd)
  have disp : Γ ⊢[PRAAx] w ≐ step H D neg :=
    canonical_unique _ _ (native zero H neg) D (qsub_canonical _ _) (ofGaussian_canonical _ _ hd) hd
      (represents_congr (.eqRefl _) (native_displacement A B neg H hs) (.eqRefl _) rep)
      (ofGaussian_represents _ _ hd)
  exact (relative_binding u v D hd hu).eqSymm.eqTrans (qmul_congr disp (.eqRefl _))

theorem sample_error (p A B D neg H K C : PTm n)
    (h : Γ ⊢[PRAAx] source A D neg) (hK : Γ ⊢[PRAAx] le one K) (hmargin : Γ ⊢[PRAAx] le D (K*A))
    (hsize : Γ ⊢[PRAAx] le (A+B+A+(B+H)) (C*D)) (hsmall : Γ ⊢[PRAAx] smallStep H K C D) : Γ ⊢[PRAAx]
    distanceBounded (qsub (ap2 nameF p (data A (B+H) D neg)) (ap2 nameF p (data A B D neg)))
      (qmul (step H D neg) (reciprocal (argument A B D neg)))
      (num 4*H*H*unit p+num 9*(A*A)) (A*A*unit p) := by
  let x := data A (B+H) D neg
  let y := data A B D neg
  let U := unit p
  let V := A*A*U
  let raw := qsub (ap2 nameF p x) (ap2 nameF p y)
  let mid := ap2 (GaussianNamedDifference.nameF nameF nameF) p (GaussianNamedDifference.data x y)
  let lin := relative (native A B neg) (native A (B+H) neg)
  have hA := h.andE₁.andE₁
  have hu := unit_positive (Γ := Γ) p
  have hv : Γ ⊢[PRAAx] le one V := positive_product _ _ (positive_product _ _ hA hA) hu
  have hi := admitted A B neg A (B+H) neg D H K C h h (native_step_bound A B neg H h.andE₁.andE₂)
    hK hmargin hmargin hsize hsmall
  have localStep : Γ ⊢[PRAAx] distanceBounded mid lin (num 4*H*H*U+num 3*(A*A)) V :=
    GaussianRightHalfPlaneLogarithmIncrement.sample_error p A B neg A (B+H) neg D H _ _ hi
  have compare : Γ ⊢[PRAAx] distanceBounded mid raw (num 6) U :=
    GaussianNamedDifference.sample_error nameF nameF x y p
      (GaussianRightHalfPlaneLogarithm.regular A (B+H) D neg h)
      (GaussianRightHalfPlaneLogarithm.regular A B D neg h)
  have first := distance_radius_mono raw mid (num 6) U (num 6*(A*A)) V hu hv
    (by dsimp only [V, U]; ipra_le 0) (distance_symmetric mid raw (num 6) U hu compare)
  exact distance_congr (.eqRefl _) (relative_vertical A B D neg H h) (by ipra_ring) (.eqRefl _)
    (distance_triangle_same raw mid lin (num 6*(A*A)) (num 4*H*H*U+num 3*(A*A)) V hv first localStep)

theorem actual_vertical_logarithm_sample_linear_error_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
    (let p := var 0
     let A := var 1
     let B := var 2
     let D := var 3
     let neg := var 4
     let H := var 5
     let K := var 6
     let C := var 7
     (source A D neg ⋏ (le one K ⋏ (le D (K*A) ⋏ (le (A+B+A+(B+H)) (C*D) ⋏ smallStep H K C D)))) ⟶
       distanceBounded (qsub (ap2 nameF p (data A (B+H) D neg)) (ap2 nameF p (data A B D neg)))
         (qmul (step H D neg) (reciprocal (argument A B D neg)))
         (num 4*H*H*unit p+num 9*(A*A)) (A*A*unit p)) :=
  closeUniv 8 (.impI (sample_error _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁
    Prf.hyp0.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₁ Prf.hyp0.andE₂.andE₂.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetLogVerticalStep
