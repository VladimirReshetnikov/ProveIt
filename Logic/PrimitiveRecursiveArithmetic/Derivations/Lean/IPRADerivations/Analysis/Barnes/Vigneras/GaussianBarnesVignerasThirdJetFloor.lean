import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasQuotientJet
import IPRADerivations.Analysis.Barnes.Vigneras.GaussianBarnesVignerasCubicForce
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper
import IPRADerivations.Analysis.RationalArithmetic.Representations.GaussianRationalValueEquality

/-! The third observation of the actual quotient jet satisfies a quantitative
lower bound on sufficiently far positive rational charts. The physical translation
can be fixed before choosing the observation clock. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesVignerasThirdJetFloor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (re)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF constant_at)
open GaussianNamedPositiveExponentialOrder (realOrder real_order_at scalar_coordinate_distance)
open GaussianRationalDistanceOrder (distance_symmetric)
open GaussianRationalHorner (qzero positive_product)
open GaussianRationalMetric (distanceBounded qsub squaredTolerance qnormSq)
open GaussianRationalValueEquality (commonDen leftValue rightValue common_den_positive
  common_left_represents common_right_represents difference_represents)
open PolynomialBisection (zle_scale_cancel slack)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle upper_of_radius)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "L" => GaussianBarnesCanonicalThirdLogarithmCofinal.nameF
local notation "ld" => GaussianBarnesCanonicalThirdLogarithmCofinal.data
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

private theorem zero_rep : Γ ⊢[PRAAx] RationalArithmetic.represents (fstT (qzero : PTm n)) (ZT.ofNat zero) one :=
  GaussianRationalHorner.scalar_congr (.eqRefl _)
    (ZT.derive (by rw [GaussianRootAlgebra.re_zero,ZT.toZ_ofNat]; ipra_simps)) (.eqRefl _)
    (GaussianRationalHorner.zero_represents one).andE₁

private theorem difference_floor (a b M N : PTm n) (h : Γ ⊢[PRAAx] upper (fstT b) (fstT a) M N) :
    Γ ⊢[PRAAx] upper (fstT qzero) (fstT (qsub a b)) M N := by
  let D := commonDen a b
  let X := leftValue a b
  let Y := rightValue a b
  let v := re (GaussianRootAlgebra.sub X Y)
  have hD := common_den_positive (Γ := Γ) a b
  have u := to_signed (fstT b) (fstT a) (re Y) (re X) D D M N
    (common_right_represents a b).andE₁ (common_left_represents a b).andE₁ h
  apply from_signed (fstT qzero) (fstT (qsub a b)) (ZT.ofNat zero) v one D M N
    (le_refl _) hD zero_rep (difference_represents a b).andE₁
  apply zle_scale_cancel (c := D) hD
  apply zle_of_toZ (slack (left (re Y) D N) (right (re X) D D M N))
  have e := zle_toZ u
  simp only [v,GaussianRootAlgebra.re_sub,left,right,slack,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat] at e ⊢
  ipra_simps
  linear_combination e

theorem sample_floor (g : PR 2) (x p q A B : PTm n)
    (hB : Γ ⊢[PRAAx] le one B) (hBA : Γ ⊢[PRAAx] le B A) (hle : Γ ⊢[PRAAx] le p q)
    (hfar : Γ ⊢[PRAAx] le (GaussianBarnesVignerasCubicForce.translation p*B) A)
    (hx : Γ ⊢[PRAAx] pointCN g x) (hg : Γ ⊢[PRAAx] realOrder constantF g qzero x) :
    Γ ⊢[PRAAx] upper (fstT qzero) (fstT (ap2 (GaussianBarnesVignerasQuotientJet.thirdF g) q
      (GaussianBarnesVignerasQuotientJet.data3 A B x))) (num 9) (unit p) := by
  let U := unit p
  let V := unit q
  let a := ap2 g q x
  let b := ap2 L q (ld A B)
  let c := ap2 (GaussianBarnesVignerasQuotientJet.thirdF g) q (GaussianBarnesVignerasQuotientJet.data3 A B x)
  let r := qsub a b
  let o : PTm n := fstT qzero
  have hU : Γ ⊢[PRAAx] le one U := unit_positive p
  have hV : Γ ⊢[PRAAx] le one V := unit_positive q
  have late : Γ ⊢[PRAAx] le U V := GaussianExponentialReference.unit_monotone hle
  have hcut := GaussianBarnesCanonicalThirdLogarithmOrder.far_decay q p A B hB hBA hfar
  have db : Γ ⊢[PRAAx] distanceBounded b qzero one U := by
    change Γ ⊢[PRAAx] RationalArgmin.rationalLE (qnormSq (qsub b qzero)) (squaredTolerance one U)
    exact RationalArgmin.rationalLE_congr (GaussianRationalModulus.norm_sub_zero b).eqSymm (.eqRefl _) hcut
  have small : Γ ⊢[PRAAx] upper (fstT b) o one U :=
    upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hU db)
  have sign : Γ ⊢[PRAAx] upper o (fstT a) (V+V) (V*V) :=
    upper_congr (congrFst (constant_at q qzero)) (.eqRefl _) (.eqRefl _) (.eqRefl _)
      (real_order_at constantF g qzero x q q hg)
  have s := upper_triangle _ _ _ _ _ _ _ small sign
  have sFit : Γ ⊢[PRAAx] le ((one*(V*V)+(V+V)*U)*U) (num 3*(U*(V*V))) := by
    ipra_le 2*𝔞 U*𝔞 V*sl late
  have raw : Γ ⊢[PRAAx] upper o (fstT r) (num 3) U :=
    difference_floor a b _ _ (upper_mono _ _ _ _ _ _ (positive_product U _ hU (positive_product V V hV hV)) s sFit)
  have hA := le_trans hB hBA
  have reg := GaussianBarnesCanonicalThirdLogarithmCofinal.regular A B (.andI hA hB)
  have err : Γ ⊢[PRAAx] distanceBounded c r (num 6) V :=
    GaussianNamedDifference.sample_error g L x (ld A B) q hx reg
  have near : Γ ⊢[PRAAx] upper (fstT r) (fstT c) (num 6) V :=
    upper_of_radius _ _ _ _ (scalar_coordinate_distance _ _ _ _ hV (distance_symmetric _ _ _ _ hV err))
  have measured := upper_triangle _ _ _ _ _ _ _ raw near
  have fit : Γ ⊢[PRAAx] le ((num 3*V+num 6*U)*U) (num 9*(U*V)) := by
    ipra_le 6*𝔞 U*sl late
  exact upper_mono _ _ _ _ _ _ (positive_product U V hU hV) measured fit

end LeanProofs.IPRA.Analysis.GaussianBarnesVignerasThirdJetFloor
