import IPRADerivations.Analysis.GaussianRationalNaturalScale
import IPRADerivations.Analysis.GaussianRationalSyntheticDivision
import IPRADerivations.Analysis.RationalRepresentedUpper

/-!
# Positive natural scaling preserves and reflects scalar order

Both Gaussian codes are expressed on one common representation
denominator. Exact scaling of their signed real numerators gives
the corresponding scaling of the rational tolerance.
-/

set_option autoImplicit false
set_option maxHeartbeats 720000

namespace LeanProofs.IPRA.Analysis.GaussianRationalNaturalScaleOrder

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (scale re)
open GaussianRationalHorner (represents positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalNaturalScale (natScale natScale_represents)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRootAlgebra (re_scale)
open RationalRepresentedUpper (to_signed from_signed left right)
open RationalValueBounds (upper)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private def commonDen (x y : PTm n) : PTm n := rawDen x*rawDen y
private def firstNum (x y : PTm n) : PTm n := scale (rawDen y) (rawGaussian x)
private def secondNum (x y : PTm n) : PTm n := scale (rawDen x) (rawGaussian y)

private theorem common_positive (x y : PTm n) : Γ ⊢[PRAAx] le one (commonDen x y) :=
  positive_product _ _ (raw_den_positive x) (raw_den_positive y)

private theorem common (x y : PTm n) : Γ ⊢[PRAAx]
    represents x (firstNum x y) (commonDen x y) ⋏ represents y (secondNum x y) (commonDen x y) :=
  .andI (rescale_to _ _ _ _ _ (raw_represents x) (.eqRefl _))
    (rescale_to _ _ _ _ _ (raw_represents y) (mul_comm _ _))

theorem scale_upper (t x y A P : PTm n) (h : Γ ⊢[PRAAx] upper (fstT x) (fstT y) A P) :
    Γ ⊢[PRAAx] upper (fstT (natScale t x)) (fstT (natScale t y)) (t*A) P := by
  let D := commonDen x y
  let X := firstNum x y
  let Y := secondNum x y
  let l := left (re X) D P
  let r := right (re Y) D D A P
  have hd := common_positive (Γ := Γ) x y
  have reps := common (Γ := Γ) x y
  have xc := natScale_represents t x X D hd reps.andE₁
  have yc := natScale_represents t y Y D hd reps.andE₂
  have signed : Γ ⊢[PRAAx] zle l r := to_signed _ _ _ _ _ _ _ _ reps.andE₁.andE₁ reps.andE₂.andE₁ h
  have eq := zle_toZ signed
  apply from_signed _ _ _ _ _ _ _ _ hd hd xc.andE₁ yc.andE₁
  apply zle_of_toZ (t*PolynomialBisection.slack l r)
  simp only [l,r,PolynomialBisection.slack,left,right,re_scale,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul] at eq ⊢
  linear_combination Groth.ι (IPRA.Q.mk Γ t)*eq

theorem reflect_upper (t x y A P : PTm n)
    (h : Γ ⊢[PRAAx] upper (fstT (natScale t x)) (fstT (natScale t y)) A P) :
    Γ ⊢[PRAAx] upper (fstT x) (fstT y) A (t*P) := by
  let D := commonDen x y
  let X := firstNum x y
  let Y := secondNum x y
  let l := left (re (scale t X)) D P
  let r := right (re (scale t Y)) D D A P
  have hd := common_positive (Γ := Γ) x y
  have reps := common (Γ := Γ) x y
  have xc := natScale_represents t x X D hd reps.andE₁
  have yc := natScale_represents t y Y D hd reps.andE₂
  have signed : Γ ⊢[PRAAx] zle l r := to_signed _ _ _ _ _ _ _ _ xc.andE₁ yc.andE₁ h
  have eq := zle_toZ signed
  apply from_signed _ _ _ _ _ _ _ _ hd hd reps.andE₁.andE₁ reps.andE₂.andE₁
  apply zle_of_toZ (PolynomialBisection.slack l r)
  simp only [l,r,PolynomialBisection.slack,left,right,re_scale,ZT.toZ_add,ZT.toZ_mul,ZT.toZ_ofNat,IPRA.Q.mk_mul,map_mul] at eq ⊢
  linear_combination eq

end LeanProofs.IPRA.Analysis.GaussianRationalNaturalScaleOrder
