import IPRADerivations.Analysis.Exponential.RightHalfPlane.GaussianRightHalfPlaneExponentialMargin
import IPRADerivations.Analysis.Names.Branches.GaussianNamedSquareBranch
import IPRADerivations.Analysis.Names.FiniteOperations.Products.GaussianNamedProductSquare

/-!
# Recover the encoded input from the small-chart exponential

The square of the positive radial representative is the squared modulus.
The square of the literal angle exponential is the rational Cayley point.
Their product is the square of the encoded input. The computed margin
of the sum selects the correct square root in iPRA.
-/

set_option autoImplicit false
set_option maxHeartbeats 950000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneExponentialSmall

open_ipra
open GaussianArctangentCayleyValues (numerator denominator value)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaWeierstrassApproximant (constant_product_cross constant_data_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_symm cross_trans)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRightHalfPlaneArgument (smallF small_input)
open GaussianRightHalfPlaneArgumentExponential (smallExpData)
open GaussianRightHalfPlaneExponentialMargin (point productF productData height small_product_apart)
open GaussianRightHalfPlaneRadialLogarithm (normNum normDen log_source)
open GaussianRationalHorner (qmul qmul_canonical ofGaussian_represents qmul_represents positive_product)
open ComplexLogarithmRemainder (code scale mul oneCode eval_re_code eval_im_code)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul re_scale im_scale re_one im_one)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "V" => GaussianRadiusExponentialName.nameF smallF
local notation "U" => GaussianPositiveRationalHalfLogarithm.positiveF
local notation "X" => GaussianPositiveRationalHalfLogarithm.positiveData

theorem finite_square (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] qmul (fraction (normNum A B) (normDen D)) (value A B) ≐
      qmul (point A B D) (point A B D) := by
  let a := normNum A B
  let b := normDen D
  let c := numerator A B
  let z := code (ZT.ofNat A) (ZT.ofNat B)
  let h := log_source A B D hA hD
  let p := fraction a b
  let q := value A B
  let r := point A B D
  have left := qmul_represents p q (scale a oneCode) c b a h.andE₂ h.andE₁
    (ofGaussian_represents _ _ h.andE₂) (ofGaussian_represents _ _ h.andE₁)
  have rr := ofGaussian_represents (Γ := Γ) z D hD
  have right := GaussianRationalHorner.represents_rescale _ (mul z z) b a (qmul_represents r r z z D D hD hD rr rr)
  have e : Γ ⊢[PRAAx] equal (mul (scale a oneCode) c) (scale a (mul z z)) := by
    apply equal_of_values <;>
      simp only [a,z,c,numerator,re_mul,im_mul,re_scale,im_scale,re_one,im_one,eval_re_code,eval_im_code,
        ZT.toZ_sub,ZT.toZ_ofNat] <;> (try ipra_simps) <;> ring
  exact GaussianRationalHorner.canonical_unique _ _ _ _ (qmul_canonical _ _) (qmul_canonical _ _)
    (positive_product _ _ h.andE₂ h.andE₁)
    (GaussianRationalHorner.represents_congr (.eqRefl _) e (.eqRefl _) left) right

theorem product_recovery (A B D : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hB : Γ ⊢[PRAAx] le B A) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] crossEquivalent productF constantF (productData A B D) (point A B D) := by
  let a := normNum A B
  let b := normDen D
  let x := X a b
  let y := smallExpData A B
  let p := fraction a b
  let q := value A B
  let r := point A B D
  let F := multiplyF U U
  let G := multiplyF V V
  let u := multiplyData U U x x
  let v := multiplyData V V y y
  have h := log_source A B D hA hD
  have reg := GaussianPositiveRationalHalfLogarithm.regular a b h
  let x' := GaussianPositiveRationalHalfLogarithm.exponentialData a b
  let W := GaussianRadiusExponentialName.nameF GaussianPositiveRationalHalfLogarithm.nameF
  have hr := GaussianRadiusExponentialName.name_regular _ _ _
    (GaussianGammaFiniteApproximantName.exponential_input _ _ reg)
  have he := GaussianPositiveRationalHalfLogarithm.positive_cross a b h
  have hx : Γ ⊢[PRAAx] pointCN U x := by
    exact cross_trans _ _ _ _ _ _ he (cross_symm _ _ _ _ he)
  have hy : Γ ⊢[PRAAx] pointCN V y := GaussianRadiusExponentialName.name_regular _ _ _ (small_input A B hA hB)
  have radial := cross_trans _ _ _ _ _ _
    (multiply_cross U W U W x x' x x' hx hr hx hr he he)
    (GaussianPositiveRationalHalfLogarithm.exponential_square a b h)
  have angle := GaussianRightHalfPlaneArgumentExponential.small_square A B hA hB
  have parts := multiply_cross F constantF G constantF u p v q
    (multiply_fast _ _ _ _ hx hx) (constant_regular p) (multiply_fast _ _ _ _ hy hy) (constant_regular q) radial angle
  have finite := cross_trans _ _ _ _ _ _ (constant_product_cross p q)
    (cross_trans _ _ _ _ _ _ (constant_data_cross _ _ (finite_square A B D hA hD))
      (cross_symm _ _ _ _ (constant_product_cross r r)))
  have squares := cross_trans _ _ _ _ _ _ (GaussianNamedProductSquare.square_product U V x y hx hy)
    (cross_trans _ _ _ _ _ _ parts finite)
  exact GaussianNamedSquareBranch.equivalent_of_apart productF constantF (productData A B D) r (height D)
    (multiply_fast U V x y hx hy) (constant_regular r) (small_product_apart A B D hA hB hD) squares

theorem actual_right_half_plane_small_exponential_product_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      ((le one (var 0) ⋏ (le (var 1) (var 0) ⋏ le one (var 2))) ⟶
        crossEquivalent productF constantF (productData (var 0) (var 1) (var 2)) (point (var 0) (var 1) (var 2))) :=
  closeUniv 3 (.impI (product_recovery _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneExponentialSmall
