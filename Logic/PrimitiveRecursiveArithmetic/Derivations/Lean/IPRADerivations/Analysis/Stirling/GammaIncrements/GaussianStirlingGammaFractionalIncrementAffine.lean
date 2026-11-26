import IPRADerivations.Analysis.Stirling.Bounds.GaussianStirlingGlobalBoundsShiftArguments
import IPRADerivations.Analysis.RationalArithmetic.Representations.RationalRepresentedUpper

/-!
# Finite signed cancellation of weighted log-gamma inequalities

The positive rational coefficient r/b is applied on a common signed
denominator. The exact order conversion divides the existing error by
b and cancels the shared value, without deciding any sign of a
logarithmic observation.
-/

set_option autoImplicit false
set_option maxHeartbeats 550000

namespace LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrementAffine

open_ipra
open ComplexLogarithmRemainder (scale oneCode add re)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (represents represents_congr positive_product ofGaussian_represents qmul qadd qmul_represents qadd_represents)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (qsub qsub_represents)
open GaussianRationalNaturalScale (natScale natScale_represents natural_product_value)
open GaussianRationalSyntheticDivision (rescale_to)
open GaussianRootAlgebra (sub re_add re_sub re_scale)
open RationalRepresentedUpper (left right to_signed from_signed)
open RationalValueBounds (upper)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private def frameDen (x y z : PTm n) : PTm n := rawDen x*rawDen y*rawDen z
private def frameX (x y z : PTm n) : PTm n := scale (rawDen y*rawDen z) (rawGaussian x)
private def frameY (x y z : PTm n) : PTm n := scale (rawDen x*rawDen z) (rawGaussian y)
private def frameZ (x y z : PTm n) : PTm n := scale (rawDen x*rawDen y) (rawGaussian z)

private theorem frame_positive (x y z : PTm n) : Γ ⊢[PRAAx] le one (frameDen x y z) :=
  positive_product _ _ (positive_product _ _ (raw_den_positive x) (raw_den_positive y)) (raw_den_positive z)

private theorem frame (x y z : PTm n) :
    Γ ⊢[PRAAx] represents x (frameX x y z) (frameDen x y z) ⋏
      (represents y (frameY x y z) (frameDen x y z) ⋏ represents z (frameZ x y z) (frameDen x y z)) := by
  exact .andI (rescale_to _ _ _ _ _ (raw_represents x) (by dsimp [frameDen]; ipra_ring))
    (.andI (rescale_to _ _ _ _ _ (raw_represents y) (by dsimp [frameDen]; ipra_ring))
      (rescale_to _ _ _ _ _ (raw_represents z) (by dsimp [frameDen]; ipra_ring)))

private theorem scaled_represents (r b x a D : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hD : Γ ⊢[PRAAx] le one D)
    (hx : Γ ⊢[PRAAx] represents x a D) :
    Γ ⊢[PRAAx] represents (qmul (fraction r b) x) (scale r a) (b*D) :=
  represents_congr (.eqRefl _) (natural_product_value r a) (.eqRefl _)
    (qmul_represents _ _ _ _ _ _ hb hD (ofGaussian_represents _ _ hb) hx)

theorem upper_increment (x y z b r s K P : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (e : Γ ⊢[PRAAx] b ≐ r+s)
    (h : Γ ⊢[PRAAx] upper (fstT (natScale b x)) (fstT (qadd (natScale r y) (natScale s z))) K P) :
    Γ ⊢[PRAAx] upper (fstT (qsub x z)) (fstT (qmul (fraction r b) (qsub y z))) K (b*P) := by
  let D := frameDen x y z
  let X := frameX x y z
  let Y := frameY x y z
  let Z := frameZ x y z
  let a := re (scale b X)
  let c := re (add (scale r Y) (scale s Z))
  let L := left a D P
  let R := right c D D K P
  have hd : Γ ⊢[PRAAx] le one D := frame_positive x y z
  have rep := frame (Γ := Γ) x y z
  have wX := natScale_represents b x X D hd rep.andE₁
  have wY := natScale_represents r y Y D hd rep.andE₂.andE₁
  have wZ := natScale_represents s z Z D hd rep.andE₂.andE₂
  have wSum := qadd_represents _ _ _ _ D hd wY wZ
  have orig : Γ ⊢[PRAAx] zle L R :=
    to_signed _ _ a c D D K P wX.andE₁ wSum.andE₁ h
  have gap := zle_toZ orig
  have bx := qsub_represents x z X Z D hd rep.andE₁ rep.andE₂.andE₂
  have by' := scaled_represents r b (qsub y z) (sub Y Z) D hb hd
    (qsub_represents y z Y Z D hd rep.andE₂.andE₁ rep.andE₂.andE₂)
  apply from_signed _ _ _ _ _ _ _ _ hd (positive_product _ _ hb hd) bx.andE₁ by'.andE₁
  apply zle_of_toZ (b*PolynomialBisection.slack L R)
  have eq := natEq e
  simp only [Q.mk_add,map_add] at eq
  simp only [a,c,L,R,PolynomialBisection.slack,left,right,re_scale,re_add,re_sub,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,Q.mk_mul,Q.mk_add,map_mul,map_add]
    at gap ⊢
  linear_combination 𝔞 b*gap-𝔞 b*𝔞 D*𝔞 P*ZT.toZ Γ (re Z)*eq

theorem lower_increment (x v z b r K P : PTm n) (hb : Γ ⊢[PRAAx] le one b)
    (h : Γ ⊢[PRAAx] upper (fstT (natScale (r+b) z)) (fstT (qadd (natScale r v) (natScale b x))) K P) :
    Γ ⊢[PRAAx] upper (fstT (qmul (fraction r b) (qsub z v))) (fstT (qsub x z)) K (b*P) := by
  let D := frameDen x v z
  let X := frameX x v z
  let V := frameY x v z
  let Z := frameZ x v z
  let a := re (scale (r+b) Z)
  let c := re (add (scale r V) (scale b X))
  let L := left a D P
  let R := right c D D K P
  have hd : Γ ⊢[PRAAx] le one D := frame_positive x v z
  have rep := frame (Γ := Γ) x v z
  have wZ := natScale_represents (r+b) z Z D hd rep.andE₂.andE₂
  have wV := natScale_represents r v V D hd rep.andE₂.andE₁
  have wX := natScale_represents b x X D hd rep.andE₁
  have wSum := qadd_represents _ _ _ _ D hd wV wX
  have orig : Γ ⊢[PRAAx] zle L R :=
    to_signed _ _ a c D D K P wZ.andE₁ wSum.andE₁ h
  have gap := zle_toZ orig
  have by' := scaled_represents r b (qsub z v) (sub Z V) D hb hd
    (qsub_represents z v Z V D hd rep.andE₂.andE₂ rep.andE₂.andE₁)
  have bx := qsub_represents x z X Z D hd rep.andE₁ rep.andE₂.andE₂
  apply from_signed _ _ _ _ _ _ _ _ (positive_product _ _ hb hd) hd by'.andE₁ bx.andE₁
  apply zle_of_toZ (b*PolynomialBisection.slack L R)
  simp only [a,c,L,R,PolynomialBisection.slack,left,right,re_scale,re_add,re_sub,ZT.toZ_mul,ZT.toZ_add,ZT.toZ_sub,ZT.toZ_ofNat,Q.mk_mul,Q.mk_add,map_mul,map_add]
    at gap ⊢
  linear_combination 𝔞 b*gap

end LeanProofs.IPRA.Analysis.GaussianStirlingGammaFractionalIncrementAffine
