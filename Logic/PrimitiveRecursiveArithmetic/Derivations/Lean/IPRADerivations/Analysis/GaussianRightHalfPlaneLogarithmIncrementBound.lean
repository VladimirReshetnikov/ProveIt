import IPRADerivations.Analysis.GaussianRightHalfPlaneLogarithmRelativeExponential
import IPRADerivations.Analysis.GaussianRightHalfPlaneArgumentContinuity
import IPRADerivations.Analysis.GaussianRightHalfPlaneRadialContinuity
import IPRADerivations.Analysis.GaussianNamedExponentialLocalUniqueness
import IPRADerivations.Analysis.GaussianLocalLogarithmQuarterBound
import IPRADerivations.Analysis.RationalClosure

/-!
# Bounds selecting the canonical logarithm increment

The radial and angular differences are each at most one eighth on
late samples. The relative Mercator correction is at most one quarter,
which puts the actual difference inside the local exponential
uniqueness radius.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmIncrementBound

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualDomain (native)
open GaussianNamedExponentialLocalUniqueness (lateSmall)
open GaussianLocalLogarithmName (pointF)
open GaussianNameArithmetic (addF addData add_fast add_canonical sum_distance)
open GaussianNameRingLaws (add_sample_error sum_right_error three)
open GaussianNamedDifference (sample_error)
open GaussianRationalHorner (qadd qzero canonical positive_product)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianReconstructionRoots (distance_zero_iff)
open GaussianRightHalfPlaneLogarithmRelativeExponential (correctedF correctedData correctionData)
open GaussianRightHalfPlaneLogarithmRelativeStep (denominator numerator radius)
open GaussianRightHalfPlaneRadialContinuity (admission budget)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.PNTStageStep (cancel_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianRightHalfPlaneLogarithm.nameF
local notation "P" => GaussianRightHalfPlaneLogarithm.data
local notation "R" => GaussianRightHalfPlaneRadialLogarithm.nameF
local notation "U" => GaussianRightHalfPlaneRadialLogarithm.data
local notation "T" => GaussianRightHalfPlaneArgument.nameF
local notation "V" => GaussianRightHalfPlaneArgument.data
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def input (A B neg a b sign D H J M : PTm n) : Fm PTm n :=
  admission A B neg a b sign D H M ⋏
    (le one J ⋏ (le J A ⋏ (le J a ⋏
      (le (num 128*H) J ⋏ le (num 16*budget A B a b H) M))))

@[simp] theorem subst_input {m : ℕ} (σ : Fin n → PTm m) (A B neg a b sign D H J M : PTm n) :
    (input A B neg a b sign D H J M).subst σ =
      input (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ neg)
        (Syn.subst σ a) (Syn.subst σ b) (Syn.subst σ sign)
        (Syn.subst σ D) (Syn.subst σ H) (Syn.subst σ J) (Syn.subst σ M) := by
  simp [input,one]

theorem shift_input (i A B neg a b sign D H J M : PTm n) (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] input (A+i*D) B neg (a+i*D) b sign D H J
      (GaussianRightHalfPlaneRadialContinuity.shiftedLower M H D i) := by
  have small := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have h16 : Γ ⊢[PRAAx] le (num 16*H) J := le_trans
    (le_of_eq_add (d := num 112*H) (by ipra_ring)) small
  have r := GaussianRightHalfPlaneRadialContinuity.shifted_admission i A B neg a b sign D H M h.andE₁
    (le_trans h16 h.andE₂.andE₂.andE₁) (le_trans h16 h.andE₂.andE₂.andE₂.andE₁)
  exact .andI r (.andI h.andE₂.andE₁ (.andI
    (le_trans h.andE₂.andE₂.andE₁ (le_add_right _ _))
    (.andI (le_trans h.andE₂.andE₂.andE₂.andE₁ (le_add_right _ _))
      (.andI small (GaussianRightHalfPlaneRadialContinuity.shifted_smallness i A B a b D H M
        h.andE₂.andE₂.andE₂.andE₂.andE₂)))))

private theorem small_angle (p A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) (hp : Γ ⊢[PRAAx] le (num 288) (unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 T p (V A B neg)) (ap2 T p (V a b sign)) one (num 8) := by
  let u := unit p
  have hs := h.andE₂
  have hJ := hs.andE₁
  have old := GaussianRightHalfPlaneArgumentContinuity.distance_at p A B neg a b sign H J
    h.andE₁.andE₁.andE₁ h.andE₁.andE₂.andE₁.andE₁ hJ hs.andE₂.andE₁ hs.andE₂.andE₂.andE₁
    (le_trans (le_of_eq_add (d := num 127*H) (by ipra_ring)) hs.andE₂.andE₂.andE₂.andE₁)
    h.andE₁.andE₂.andE₂.andE₁
  have hl : Γ ⊢[PRAAx] le (num 8*(num 8*H*u+num 18*J)) (J*u) := by
    apply cancel_pos (c := two) (le_succ_self one)
    exact le_congr (by ipra_ring) (by ipra_ring)
      (add_le_add₂ (le_mul_mono hs.andE₂.andE₂.andE₂.andE₁ (le_refl u)) (le_mul_mono hp (le_refl J)))
  exact distance_radius_mono _ _ _ _ one (num 8) (positive_product _ _ hJ (unit_positive p))
    (by ipra_le 7) (le_congr (mul_comm _ _) (one_mul _).eqSymm hl) old

private theorem pay {a b p C : PTm n} (h : Γ ⊢[PRAAx] distanceBounded a b C (unit p)) :
    Γ ⊢[PRAAx] distanceBounded a b (num 8*C) (num 8*unit p) := by
  have h8 : Γ ⊢[PRAAx] le one (num 8) := by ipra_le 7
  exact distance_radius_mono _ _ _ _ _ _ (unit_positive p) (positive_product _ _ h8 (unit_positive p))
    (le_of_eq_add (d := zero) (by ipra_ring)) h

private theorem late_at (p A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) (hp : Γ ⊢[PRAAx] le (num 288) p) :
    Γ ⊢[PRAAx]
      canonical (ap2 (F correctedF G) p (X (correctedData A B neg a b sign D H) (P a b D sign))) ⋏
      bounded (ap2 (F correctedF G) p (X (correctedData A B neg a b sign D H) (P a b D sign))) (num 3) (num 4) := by
  let u := unit p
  let d := num 8*u
  let x := P A B D neg
  let y := P a b D sign
  let z := correctionData A B neg a b sign H
  let c := correctedData A B neg a b sign D H
  let r := ap2 G p x
  let s := ap2 G p y
  let t := ap2 correctedF p c
  let m := ap2 pointF p z
  let rh := qadd (ap2 R p (U A B D)) (ap2 T p (V A B neg))
  let sh := qadd (ap2 R p (U a b D)) (ap2 T p (V a b sign))
  let raw := qsub t s
  let delta := ap2 (F correctedF G) p (X c y)
  have h8 : Γ ⊢[PRAAx] le one (num 8) := by ipra_le 7
  have h4 : Γ ⊢[PRAAx] le one (num 4) := by ipra_le 3
  have hu := unit_positive (Γ := Γ) p
  have hd := positive_product _ _ h8 hu
  have high := le_trans hp (le_trans (le_succ_self p) (RationalClosure.succ_le_two_pow p))
  have h32 : Γ ⊢[PRAAx] le (num 32) u := le_trans (by ipra_le 256) high
  have hA := h.andE₁.andE₁
  have ha := h.andE₁.andE₂.andE₁
  have hxR := GaussianRightHalfPlaneRadialLogarithm.regular A B D hA.andE₁.andE₁ hA.andE₂
  have hyR := GaussianRightHalfPlaneRadialLogarithm.regular a b D ha.andE₁.andE₁ ha.andE₂
  have hxT := GaussianRightHalfPlaneArgument.name_regular A B neg hA.andE₁
  have hyT := GaussianRightHalfPlaneArgument.name_regular a b sign ha.andE₁
  have hx := add_fast R T (U A B D) (V A B neg) hxR hxT
  have hy := add_fast R T (U a b D) (V a b sign) hyR hyT
  have rad := GaussianRightHalfPlaneRadialContinuity.small_radial_distance p p A B neg a b sign D H M
    h.andE₁ h.andE₂.andE₂.andE₂.andE₂.andE₂ h32 h32
  have ang := small_angle p A B neg a b sign D H J M h high
  have pair := sum_distance _ _ _ _ one one (num 8) h8 (distance_symmetric _ _ _ _ h8 rad) ang
  have pair' : Γ ⊢[PRAAx] distanceBounded rh sh ((one+one)*u) d :=
    distance_radius_mono _ _ _ _ _ _ h8 hd (le_of_eq_add (d := zero) (by dsimp only [d]; ipra_ring)) pair
  have xr : Γ ⊢[PRAAx] distanceBounded r rh (num 8*three) d := pay
    (add_sample_error R T (U A B D) (V A B neg) p hxR hxT)
  have ys : Γ ⊢[PRAAx] distanceBounded sh s (num 8*three) d :=
    distance_symmetric _ _ _ _ hd (pay (add_sample_error R T (U a b D) (V a b sign) p hyR hyT))
  have b₁ := distance_triangle_same r rh sh _ _ d hd xr pair'
  have b₂ := distance_triangle_same r sh s _ _ d hd b₁ ys
  let w := native A B neg
  let e := native a b sign
  let l := numerator w e
  let N := denominator w
  let C := radius A B H
  have size := h.andE₂.andE₂.andE₂.andE₂.andE₁
  have h16 : Γ ⊢[PRAAx] le (num 16*H) A := le_trans
    (le_trans (le_of_eq_add (d := num 112*H) (by ipra_ring)) size) h.andE₂.andE₂.andE₁
  have hSmall : Γ ⊢[PRAAx] le (num 4*H) A := le_trans (le_of_eq_add (d := num 12*H) (by ipra_ring)) h16
  have source := GaussianRightHalfPlaneLogarithmRelativeStep.mercator_source A B neg e H hA.andE₁
    h.andE₁.andE₂.andE₂.andE₁ hSmall
  have tiny : Γ ⊢[PRAAx] le (num 8*C) N := by
    apply cancel_pos (c := A) hA.andE₁.andE₁
    exact le_trans (le_congr (by ipra_ring) (by ipra_ring)
      (le_mul_mono (le_refl (num 8)) (GaussianRightHalfPlaneLogarithmRelativeStep.paid_radius A B neg H hA.andE₁)))
      (le_mul_mono h16 (le_refl N))
  have mer : Γ ⊢[PRAAx] bounded m one (num 4) :=
    GaussianLocalLogarithmQuarterBound.quarter_at p l C N source tiny (le_trans (by ipra_le 284) hp)
  have mer' := distance_radius_mono m qzero one (num 4) (two*u) d h4 hd
    (le_of_eq_add (d := zero) (by dsimp only [d]; ipra_ring)) ((distance_zero_iff _ _ _ h4).iffMpr mer)
  have rCanonical : Γ ⊢[PRAAx] canonical r := add_canonical R T (U A B D) (V A B neg) p
  have back := distance_congr (.eqRefl _) (GaussianReciprocalHorner.qadd_zero_right r rCanonical) (.eqRefl _) (.eqRefl _)
    (sum_right_error r m qzero (two*u) d hd mer')
  have hm := GaussianLocalLogarithmName.name_regular l C N source
  have tr : Γ ⊢[PRAAx] distanceBounded t (qadd r m) (num 8*three) d :=
    pay (add_sample_error G pointF x z p hx hm)
  have t₁ := distance_triangle_same t (qadd r m) r _ _ d hd tr back
  have t₂ := distance_triangle_same t r s _ _ d hd t₁ b₂
  have hc := add_fast G pointF x z hx hm
  have dv : Γ ⊢[PRAAx] distanceBounded delta raw (num 8*num 6) d := pay (sample_error correctedF G c y p hc hy)
  have toZero := (distance_zero_iff raw _ _ hd).iffMpr t₂
  have all := distance_triangle_same delta raw qzero _ _ d hd dv toZero
  have coarse : Γ ⊢[PRAAx] distanceBounded delta qzero (num 4*u+num 120) d :=
    distance_congr (.eqRefl _) (.eqRefl _) (by unfold three; ipra_ring) (.eqRefl _) all
  have atLeast60 : Γ ⊢[PRAAx] le (num 60) u := le_trans (by ipra_le 228) high
  have budgetOK : Γ ⊢[PRAAx] le ((num 4*u+num 120)*num 4) (num 3*(num 8*u)) := by
    ipra_le 8*sl atLeast60
  have paid := distance_radius_mono delta qzero (num 4*u+num 120) d (num 3) (num 4) hd h4 budgetOK coarse
  exact .andI (add_canonical correctedF (GaussianNameRingLaws.negativeF G) c (GaussianNameRingLaws.negativeData y) p)
    ((distance_zero_iff delta _ _ h4).iffMp paid)

theorem late_difference (A B neg a b sign D H J M : PTm n)
    (h : Γ ⊢[PRAAx] input A B neg a b sign D H J M) :
    Γ ⊢[PRAAx] lateSmall (F correctedF G) (X (correctedData A B neg a b sign D H) (P a b D sign)) (num 288) := by
  refine .allI (.impI ?_)
  let sh (x : PTm n) := Syn.shift x
  let Δ := le (num 288) (var 0) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] input (sh A) (sh B) (sh neg) (sh a) (sh b) (sh sign) (sh D) (sh H) (sh J) (sh M) := by
    simpa only [Fm.shift,Syn.shift,subst_input,Δ,sh] using h.shift.wk
  simpa only [lateSmall,Syn.shift,GaussianNamedDifference.subst_data,GaussianRightHalfPlaneLogarithm.subst_data,
    GaussianRightHalfPlaneLogarithmRelativeExponential.subst_correctedData,LeanProofs.IPRA.PTm.subst_num,Δ,sh] using
    late_at (var 0) (sh A) (sh B) (sh neg) (sh a) (sh b) (sh sign) (sh D) (sh H) (sh J) (sh M)
      hs (Prf.hyp0 : Δ ⊢[PRAAx] le (num 288) (var 0))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneLogarithmIncrementBound
