import IPRADerivations.Analysis.GaussianRaabeLogPrimitiveCell
import IPRADerivations.Analysis.GaussianRationalInverseQuadraticAlgebra

/-!
# The elementary Stirling term on a far unit interval

At a point a distance at most one into the interval, the elementary
Stirling term has an affine approximation centered at the midpoint.
The ordinary positive logarithm supplies the original observations.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianRaabeStirlingCell

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianPositiveRationalLogarithm (fraction sample)
open GaussianPositiveRationalLogarithmIncrement (increment original_increment)
open GaussianRaabeLogPrimitiveCell (primitive area fraction_bound)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_triangle_same)
open GaussianRationalHorner (positive_product qadd qmul qzero)
open GaussianRationalMetric (bounded distanceBounded qsub)
open GaussianRationalReciprocal (bounded_difference bounded_product bound_congr)
open GaussianRationalRoundedPower (multiplication_difference)
open GaussianRationalSyntheticDivision (qmul_congr qsub_congr)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def half : PTm n := fraction one two

def elementary (p A D : PTm n) : PTm n := qsub (primitive p A D) (qmul half (sample p A D))

def affine (p A D H : PTm n) : PTm n :=
  qadd (primitive p A D) (qmul (qsub (fraction H D) half) (sample p A D))

def coefficient (p A D : PTm n) : PTm n := num 4*(D*D)*unit p+num 4*(A*A)+A*D
def denominator (p A D : PTm n) : PTm n := A*D*unit p

@[simp] theorem subst_half {m : ℕ} (σ : Fin n → PTm m) :
    Syn.subst σ (half : PTm n) = (half : PTm m) := by simp [half,one,two]
@[simp] theorem subst_elementary {m : ℕ} (σ : Fin n → PTm m) (p A D : PTm n) :
    Syn.subst σ (elementary p A D) = elementary (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ D) := by
  simp [elementary]
@[simp] theorem subst_affine {m : ℕ} (σ : Fin n → PTm m) (p A D H : PTm n) :
    Syn.subst σ (affine p A D H) = affine (Syn.subst σ p) (Syn.subst σ A) (Syn.subst σ D) (Syn.subst σ H) := by
  simp [affine]

private theorem subtract_product (a b l : PTm n) :
    Γ ⊢[PRAAx] qmul (qsub a b) l ≐ qsub (qmul a l) (qmul b l) :=
  (GaussianRationalPowerAlgebra.qmul_commutative (qsub a b) l).eqTrans
    ((multiplication_difference l a b).eqSymm.eqTrans
      (qsub_congr (GaussianRationalPowerAlgebra.qmul_commutative l a)
        (GaussianRationalPowerAlgebra.qmul_commutative l b)))

theorem elementary_at (p A D : PTm n) :
    Γ ⊢[PRAAx] elementary p A D ≐
      qsub (qmul (qsub (fraction A D) half) (sample p A D)) (fraction A D) := by
  let x := fraction A D
  let l := sample p A D
  let g := qmul x l
  let h := qmul half l
  exact (GaussianRationalInverseQuadraticAlgebra.subtract_sum g x h).eqTrans
    ((qsub_congr (.eqRefl g) (GaussianReciprocalHorner.qadd_commutative x h)).eqTrans
      ((GaussianRationalInverseQuadraticAlgebra.subtract_sum g h x).eqSymm.eqTrans
        (qsub_congr (subtract_product x half l).eqSymm (.eqRefl x))))

private theorem affine_defect (p A D H : PTm n) :
    Γ ⊢[PRAAx] qsub (elementary p (A+H) D) (affine p A D H) ≐
      qsub (qsub (qsub (primitive p (A+H) D) (primitive p A D)) (area p A D H))
        (qmul half (increment p p A D H)) := by
  let y := primitive p (A+H) D
  let x := primitive p A D
  let l := sample p A D
  let m := sample p (A+H) D
  let a := area p A D H
  let b := qmul half l
  have ea : Γ ⊢[PRAAx] affine p A D H ≐ qsub (qadd x a) b :=
    (GaussianRationalSyntheticDivision.qadd_congr (.eqRefl x) (subtract_product (fraction H D) half l)).eqTrans
      ((GaussianRationalSumAlgebra.qadd_associative x a (GaussianRationalMetric.qnegative b)).eqSymm)
  exact (qsub_congr (.eqRefl _) ea).eqTrans
    ((GaussianNamedDifferenceAlgebra.rational_shuffle y (qmul half m) (qadd x a) b).eqTrans
      (qsub_congr (GaussianRationalInverseQuadraticAlgebra.subtract_sum y x a).eqSymm
        (multiplication_difference half m l)))

private theorem primitive_bound (p A D H : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hDA : Γ ⊢[PRAAx] le D A) (hHD : Γ ⊢[PRAAx] le H D) :
    Γ ⊢[PRAAx] bounded (qsub (qsub (primitive p (A+H) D) (primitive p A D)) (area p A D H))
      (num 3*(D*D)*unit p+num 4*(A*A)) (denominator p A D) := by
  let U := unit p
  have hA := le_trans hD hDA
  have hHA := le_trans hHD hDA
  have hs := le_mul_mono hHD hHD
  have hu := unit_positive (Γ := Γ) p
  have old := positive_product _ _ (positive_product _ _ hD (positive_product _ _ hA hA)) hu
  have new := positive_product _ _ (positive_product _ _ hA hD) hu
  exact distance_radius_mono _ _ _ _ _ _ old new (by
    dsimp only [GaussianRaabeLogPrimitiveCell.numerator,GaussianRaabeLogPrimitiveCell.denominator,denominator]
    ipra_le 3*𝔞(A)^2*𝔞(D)*𝔞(U)^2*sl hs +
      (𝔞(A)*𝔞(D)*𝔞(U)^2*𝔞(H)^2+2*𝔞(D)*𝔞(A)^3*𝔞(U))*sl hHA)
    (GaussianRaabeLogPrimitiveCell.cell_error p A D H hA hD)

private theorem log_bound (p A D H : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hDA : Γ ⊢[PRAAx] le D A) (hHD : Γ ⊢[PRAAx] le H D) :
    Γ ⊢[PRAAx] bounded (qmul half (increment p p A D H)) (D*D*unit p+A*D) (denominator p A D) := by
  let U := unit p
  let v := increment p p A D H
  let c := fraction H A
  have hA := le_trans hD hDA
  have hu := unit_positive (Γ := Γ) p
  have ha := positive_product _ _ hA hA
  let W := A*A*U
  have hw : Γ ⊢[PRAAx] le one W := positive_product _ _ ha hu
  have first : Γ ⊢[PRAAx] distanceBounded v c (H*H*U+two*(A*A)) W :=
    distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ha (positive_product _ _ hu hu)) hw
      (le_of_eq_add (d := zero)
        (by dsimp only [U,W,GaussianPositiveRationalLogarithmIncrement.errorNumerator,
          GaussianPositiveRationalLogarithmIncrement.errorDenominator]; ipra_ring))
      (original_increment p p A D H hA hD)
  have second : Γ ⊢[PRAAx] distanceBounded c qzero (H*A*U) W :=
    distance_radius_mono _ _ _ _ _ _ hA hw
      (le_of_eq_add (d := zero) (by dsimp only [W]; ipra_ring))
      ((GaussianReconstructionRoots.distance_zero_iff c H A hA).iffMpr (fraction_bound H A hA))
  have square : Γ ⊢[PRAAx] le (H*H) (D*A) := le_mul_mono hHD (le_trans hHD hDA)
  have small := mul_le_mul_right A hHD
  have haU := positive_product A U hA hu
  have compressed : Γ ⊢[PRAAx] distanceBounded v qzero (two*D*U+two*A) (A*U) :=
    distance_radius_mono _ _ _ _ _ _ hw haU (by
      dsimp only [W]
      ipra_le 𝔞(A)*𝔞(U)^2*sl square+𝔞(A)*𝔞(U)^2*sl small)
      (distance_triangle_same _ _ _ _ _ _ hw first second)
  have ht : Γ ⊢[PRAAx] le one (two : PTm n) := RationalAlgebra.two_positive
  have b := bounded_product half v one two (two*D*U+two*A) (A*U) ht haU
    (fraction_bound one two ht) ((GaussianReconstructionRoots.distance_zero_iff _ _ _ haU).iffMp compressed)
  have near : Γ ⊢[PRAAx] distanceBounded (qmul half v) qzero (one*(two*D*U+two*A)) (two*(A*U)) :=
    (GaussianReconstructionRoots.distance_zero_iff _ _ _ (positive_product _ _ ht haU)).iffMpr b
  have hden := positive_product _ _ (positive_product _ _ hA hD) hu
  exact (GaussianReconstructionRoots.distance_zero_iff _ _ _ hden).iffMp
    (distance_radius_mono _ _ _ _ _ _ (positive_product _ _ ht haU) hden
      (le_of_eq_add (d := zero) (by dsimp only [denominator,U]; ipra_ring)) near)

theorem cell_error (p A D H : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (hDA : Γ ⊢[PRAAx] le D A) (hHD : Γ ⊢[PRAAx] le H D) :
    Γ ⊢[PRAAx] distanceBounded (elementary p (A+H) D) (affine p A D H)
      (coefficient p A D) (denominator p A D) := by
  let U := unit p
  let W := denominator p A D
  have hw := positive_product _ _ (positive_product _ _ (le_trans hD hDA) hD) (unit_positive p)
  have raw := bounded_difference _ _ (num 3*(D*D)*U+num 4*(A*A)) W (D*D*U+A*D) W hw hw
    (primitive_bound p A D H hD hDA hHD) (log_bound p A D H hD hDA hHD)
  have moved := bound_congr (affine_defect (Γ := Γ) p A D H).eqSymm (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hw hw) hw
    (le_of_eq_add (d := zero) (by dsimp only [coefficient,W,U,denominator]; ipra_ring)) moved

theorem actual_positive_Stirling_elementary_affine_cell_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      (let p := var 0
       let A := var 1
       let D := var 2
       let H := var 3
       (le one D ⋏ (le D A ⋏ le H D)) ⟶
         distanceBounded (elementary p (A+H) D) (affine p A D H)
           (coefficient p A D) (denominator p A D)) :=
  closeUniv 4 (.impI (cell_error _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRaabeStirlingCell
