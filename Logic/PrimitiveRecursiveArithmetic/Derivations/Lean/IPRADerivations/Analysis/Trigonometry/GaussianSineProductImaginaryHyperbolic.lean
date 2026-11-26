import IPRADerivations.Analysis.Names.GaussianNamedImaginaryProduct
import IPRADerivations.Analysis.Trigonometry.GaussianPiRationalScale
import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryCofinalDerivative
import IPRADerivations.Analysis.Trigonometry.GaussianSineProductImaginaryFirstOrderBound
import IPRADerivations.Analysis.Trigonometry.GaussianSineProductT7Actual

/-!
# The original imaginary sine product and the original hyperbolic sine

At (z=iA/B), the published sine product is equivalent to the hyperbolic
identity `sinh(π A/B) = (π A/B) P(A/B)`. The hyperbolic side is built from
the actual independent exponential names on the signed π scalings.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryHyperbolic

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (eval_re_code eval_im_code)
open GaussianArctangentCayleyValues (imaginaryCode imaginaryPoint)
open GaussianBoundedConstantProductName (constantF constant_regular)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaWeierstrassApproximant (constant_data_cross constant_product_cross)
open GaussianNameArithmetic (multiplyF multiplyData multiply_fast)
open GaussianNameEquivalence (crossEquivalent cross_refl cross_symm cross_trans cross_to_diagonal)
open GaussianNameRingLaws (multiply_associative multiply_commutative negativeF negativeData negative_fast negative_equivalent)
open GaussianNamedSineTaylor (imaginaryF imaginary_input)
open GaussianRationalHorner (ofGaussian ofGaussian_represents ofGaussian_canonical qmul qmul_canonical qmul_represents
  canonical_unique represents_congr)
open GaussianRootAlgebra (equal equal_of_values re_mul im_mul re_neg im_neg)
open GaussianSineProductImaginaryLogDerivative (axisNumerator realNumerator)
open GaussianSineProductImaginaryCofinalDerivative (sineData)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "Scale" => GaussianPiRationalScale.nameF
local notation "Pi" => GaussianGammaHalfPiName.nameF
local notation "Product" => GaussianSineProductName.nameF
local notation "argumentF" => GaussianGammaReflectionSineTransfer.argumentF
local notation "Exp" => GaussianRadiusExponentialName.nameF
local notation "Diff" => GaussianNamedDifference.nameF

def expF : PR 2 := Exp Scale
def expData (s : Bool) (A B R x : PTm n) : PTm n :=
  GaussianRadiusExponentialName.data (R*GaussianNameBounds.U Pi x) (GaussianPiRationalScale.data s A B R x)
def sinhF : PR 2 := multiplyF constantF (Diff expF expF)
def sinhData (A B R x : PTm n) : PTm n := multiplyData constantF (Diff expF expF)
  (GaussianPiRationalScale.point true one two) (GaussianNamedDifference.data (expData true A B R x) (expData false A B R x))
def productF : PR 2 := multiplyF Scale Product
def productData (A B R x : PTm n) : PTm n :=
  multiplyData Scale Product (GaussianPiRationalScale.data false A B R x) (sineData A B R)

private theorem bring_middle (f g h : PR 2) (x y z : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y) (hh : Γ ⊢[PRAAx] pointCN h z) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF f (multiplyF g h)) (multiplyF (multiplyF f h) g)
      (multiplyData f (multiplyF g h) x (multiplyData g h y z))
      (multiplyData (multiplyF f h) g (multiplyData f h x z) y) := by
  have changeInner := multiply_cross f f _ _ x x _ _ hf hf
    (multiply_fast g h y z hg hh) (multiply_fast h g z y hh hg) (cross_refl f x hf)
    (multiply_commutative g h y z hg hh)
  exact cross_trans _ _ _ _ _ _ changeInner (cross_symm _ _ _ _ (multiply_associative f h g x z y hf hh hg))

private theorem constant_group (f : PR 2) (a b q x : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (h : Γ ⊢[PRAAx] qmul a b ≐ q) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF (multiplyF constantF f)) (multiplyF constantF f)
      (multiplyData constantF (multiplyF constantF f) a (multiplyData constantF f b x))
      (multiplyData constantF f q x) := by
  have ha := constant_regular (Γ := Γ) a
  have hb := constant_regular (Γ := Γ) b
  have fixed := cross_trans _ _ _ _ _ _ (constant_product_cross a b) (constant_data_cross _ _ h)
  have lift := multiply_cross _ _ f f _ _ x x (multiply_fast _ _ _ _ ha hb) (constant_regular q) hf hf fixed
    (cross_refl f x hf)
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (multiply_associative constantF constantF f a b x ha hb hf)) lift

private theorem difference_cross (f g h k : PR 2) (x y u v : PTm n)
    (hf : Γ ⊢[PRAAx] pointCN f x) (hg : Γ ⊢[PRAAx] pointCN g y)
    (hh : Γ ⊢[PRAAx] pointCN h u) (hk : Γ ⊢[PRAAx] pointCN k v)
    (e : Γ ⊢[PRAAx] crossEquivalent f h x u) (t : Γ ⊢[PRAAx] crossEquivalent g k y v) :
    Γ ⊢[PRAAx] crossEquivalent (Diff f g) (Diff h k) (GaussianNamedDifference.data x y) (GaussianNamedDifference.data u v) :=
  GaussianNamedGammaHalfShift.add_cross f h (negativeF g) (negativeF k) x u (negativeData y) (negativeData v)
    hf hh (negative_fast g y hg) (negative_fast k v hk) e
    (negative_equivalent g k y v hg hk (cross_to_diagonal _ _ _ _ t))

private def negativeImaginary : PTm n := ofGaussian (ComplexLogarithmRemainder.neg imaginaryCode) one

private theorem rotate_axis (A B : PTm n) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] qmul negativeImaginary (ofGaussian (axisNumerator A) B) ≐ GaussianPiRationalScale.point false A B := by
  let ni := ComplexLogarithmRemainder.neg (imaginaryCode : PTm n)
  have raw := qmul_represents _ _ _ _ _ _ (le_refl one) hB
    (ofGaussian_represents (Γ := Γ) ni one (le_refl one)) (ofGaussian_represents (axisNumerator A) B hB)
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul ni (axisNumerator A)) (realNumerator A) := by
    dsimp only [ni]
    apply equal_of_values <;> simp only [re_mul, im_mul, re_neg, im_neg, imaginaryCode, axisNumerator,
      realNumerator, eval_re_code, eval_im_code, ZT.toZ_ofNat] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ B (qmul_canonical _ _) (ofGaussian_canonical _ _ hB) hB
    (represents_congr (.eqRefl _) e (one_mul B) raw) (ofGaussian_represents _ _ hB)

private theorem rotate_multiplier :
    Γ ⊢[PRAAx] qmul negativeImaginary GaussianNamedSineFromExponential.multiplier ≐ GaussianPiRationalScale.point true one two := by
  let ni := ComplexLogarithmRemainder.neg (imaginaryCode : PTm n)
  have htwo : Γ ⊢[PRAAx] le one two := le_succ_self one
  have raw := qmul_represents _ _ _ _ _ _ (le_refl one) htwo
    (ofGaussian_represents (Γ := Γ) ni one (le_refl one)) (ofGaussian_represents ni two htwo)
  have e : Γ ⊢[PRAAx] equal (ComplexLogarithmRemainder.mul ni ni)
      (ComplexLogarithmRemainder.neg (realNumerator one)) := by
    dsimp only [ni]
    apply equal_of_values <;> simp only [re_mul, im_mul, re_neg, im_neg, imaginaryCode,
      realNumerator, eval_re_code, eval_im_code, ZT.toZ_ofNat] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ two (qmul_canonical _ _) (ofGaussian_canonical _ _ htwo) htwo
    (represents_congr (.eqRefl _) e (one_mul two) raw) (ofGaussian_represents _ _ htwo)

theorem as_negative_pi (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent (imaginaryF argumentF) Scale
      (GaussianGammaReflectionSineTransfer.argumentData (axisNumerator A) B x) (GaussianPiRationalScale.data true A B R x) := by
  let z := ofGaussian (axisNumerator A) B
  let i := (imaginaryPoint : PTm n)
  let c := GaussianPiRationalScale.point true A B
  let arg := GaussianGammaReflectionSineTransfer.argumentData (axisNumerator A) B x
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have hz := constant_regular (Γ := Γ) z
  have hi := constant_regular (Γ := Γ) i
  have ha : Γ ⊢[PRAAx] pointCN argumentF arg := multiply_fast Pi constantF x z hp hz
  have rotation := GaussianNamedImaginaryProduct.ordinary_product argumentF arg ha
  have reordered := bring_middle constantF Pi constantF i x z hi hp hz
  have fixed := cross_trans _ _ _ _ _ _ (constant_product_cross i z)
    (constant_data_cross _ c (GaussianPiRationalScale.imaginary_axis_point A B hB))
  have lift := multiply_cross _ _ Pi Pi _ _ x x (multiply_fast _ _ _ _ hi hz) (constant_regular c) hp hp fixed
    (cross_refl Pi x hp)
  exact cross_trans _ _ _ _ _ _ rotation (cross_trans _ _ _ _ _ _ reordered
    (cross_trans _ _ _ _ _ _ lift (cross_symm _ _ _ _ (GaussianPiRationalScale.ordinary true A B R x hB hA))))

private theorem rotated_sine (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF GaussianGammaReflectionSineTransfer.sineAtPiF) sinhF
      (multiplyData constantF GaussianGammaReflectionSineTransfer.sineAtPiF negativeImaginary
        (GaussianGammaReflectionSineTransfer.sineAtPiData (axisNumerator A) B x)) (sinhData A B R x) := by
  let z := axisNumerator A
  let a := GaussianGammaReflectionSineTransfer.argumentData z B x
  let U := GaussianGammaReflectionSineTransfer.argumentRadius z B x
  let V := R*GaussianNameBounds.U Pi x
  let I := imaginaryF argumentF
  let w := GaussianPiRationalScale.data true A B R x
  let u := GaussianPiRationalScale.data false A B R x
  let m := (GaussianNamedSineFromExponential.multiplier : PTm n)
  let c := GaussianPiRationalScale.point true one (two : PTm n)
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have ha : Γ ⊢[PRAAx] pointCN argumentF a := multiply_fast Pi constantF x (ofGaussian z B) hp (constant_regular _)
  have hi : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input I U a :=
    imaginary_input _ _ _ (GaussianGammaFiniteApproximantName.exponential_input argumentF a ha)
  have hw : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input Scale V w :=
    GaussianPiRationalScale.exponential_input true A B R x hB hA
  have hu : Γ ⊢[PRAAx] GaussianRadiusExponentialName.input Scale V u :=
    GaussianPiRationalScale.exponential_input false A B R x hB hA
  have negI := GaussianExponentialInverse.negative_input I U a hi
  have hneg := as_negative_pi A B R x hB hA
  have hpos := cross_trans _ _ _ _ _ _
    (negative_equivalent I Scale a w hi.andE₁ hw.andE₁ (cross_to_diagonal _ _ _ _ hneg))
    (GaussianPiRationalScale.negation true A B R x hB hA)
  have eneg := GaussianExponentialRadiusIndependence.independent_radii_proper I Scale U V a w hi hw hneg
  have epos := GaussianExponentialRadiusIndependence.independent_radii_proper (negativeF I) Scale U V (negativeData a) u negI hu hpos
  have p₁ := GaussianRadiusExponentialName.name_regular _ _ _ hi
  have p₂ := GaussianRadiusExponentialName.name_regular _ _ _ negI
  have q₁ := GaussianRadiusExponentialName.name_regular _ _ _ hw
  have q₂ := GaussianRadiusExponentialName.name_regular _ _ _ hu
  have hdiff := difference_cross _ _ _ _ _ _ _ _ p₁ p₂ q₁ q₂ eneg epos
  have red := constant_group (GaussianNamedSineFromExponential.differenceF I) negativeImaginary m c
    (GaussianNamedSineFromExponential.differenceData U a) (GaussianNamedDifference.name_regular _ _ _ _ p₁ p₂) rotate_multiplier
  have lift := multiply_cross constantF constantF _ _ c c _ _ (constant_regular c) (constant_regular c)
    (GaussianNamedDifference.name_regular _ _ _ _ p₁ p₂) (GaussianNamedDifference.name_regular _ _ _ _ q₁ q₂)
    (cross_refl _ _ (constant_regular c)) hdiff
  exact cross_trans _ _ _ _ _ _ red lift

private theorem rotated_product (A B R x : PTm n) (hB : Γ ⊢[PRAAx] le one B) (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF constantF (multiplyF Pi GaussianGammaReflectionProduct.productLinearF)) productF
      (multiplyData constantF (multiplyF Pi GaussianGammaReflectionProduct.productLinearF) negativeImaginary
        (multiplyData Pi GaussianGammaReflectionProduct.productLinearF x
          (GaussianGammaReflectionProduct.productLinearData (axisNumerator A) R B))) (productData A B R x) := by
  let z := ofGaussian (axisNumerator A) B
  let a := (negativeImaginary : PTm n)
  let c := GaussianPiRationalScale.point false A B
  let y := sineData A B R
  let L := GaussianGammaReflectionProduct.productLinearF
  let v := GaussianGammaReflectionProduct.productLinearData (axisNumerator A) R B
  have ha := constant_regular (Γ := Γ) a
  have hc := constant_regular (Γ := Γ) c
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have hy : Γ ⊢[PRAAx] pointCN Product y :=
    GaussianSineProductName.name_regular _ _ _ hB (GaussianSineProductImaginaryFirstOrderBound.axis_disk A B R hA)
  have hv : Γ ⊢[PRAAx] pointCN L v := multiply_fast constantF Product z y (constant_regular z) hy
  have reorder := bring_middle constantF Pi L a x v ha hp hv
  have reduce := constant_group Product a z c y hy (rotate_axis A B hB)
  have lift := multiply_cross _ _ Pi Pi _ _ x x (multiply_fast _ _ _ _ ha hv)
    (multiply_fast constantF Product c y hc hy) hp hp reduce (cross_refl Pi x hp)
  have permute := cross_trans _ _ _ _ _ _
    (multiply_associative constantF Product Pi c y x hc hy hp)
    (bring_middle constantF Product Pi c y x hc hy hp)
  have hs := GaussianPiRationalScale.regular false A B R x hB hA
  have last := multiply_cross _ Scale Product Product _ _ y y (multiply_fast constantF Pi c x hc hp)
    hs hy hy (cross_symm _ _ _ _ (GaussianPiRationalScale.ordinary false A B R x hB hA)) (cross_refl Product y hy)
  exact cross_trans _ _ _ _ _ _ reorder (cross_trans _ _ _ _ _ _ lift (cross_trans _ _ _ _ _ _ permute last))

theorem sinh_as_product (A B R x : PTm n) (hR : Γ ⊢[PRAAx] le one R) (hB : Γ ⊢[PRAAx] le one B)
    (hA : Γ ⊢[PRAAx] le A (R*B)) :
    Γ ⊢[PRAAx] crossEquivalent sinhF productF (sinhData A B R x) (productData A B R x) := by
  let z := axisNumerator A
  let a := GaussianGammaReflectionSineTransfer.argumentData z B x
  let U := GaussianGammaReflectionSineTransfer.argumentRadius z B x
  let Si := GaussianGammaReflectionSineTransfer.sineAtPiF
  let L := GaussianGammaReflectionProduct.productLinearF
  let v := GaussianGammaReflectionProduct.productLinearData z R B
  have hd := GaussianSineProductImaginaryFirstOrderBound.axis_disk A B R hA
  have source : Γ ⊢[PRAAx] GaussianGammaCanonicalExponent.source z R B := .andI hR (.andI hB hd)
  have hs := GaussianSineProductT7Actual.original_product_identification z R B x source
  have exactSine := GaussianGammaReflectionSineTransfer.sine_as_product z R B x source hs
  have hp := GaussianGammaHalfPiName.name_regular (Γ := Γ) x
  have ha : Γ ⊢[PRAAx] pointCN argumentF a :=
    multiply_fast Pi constantF x (ofGaussian z B) hp (constant_regular _)
  have si : Γ ⊢[PRAAx] pointCN Si (GaussianGammaReflectionSineTransfer.sineAtPiData z B x) :=
    GaussianNamedSineFromExponential.sine_regular (imaginaryF argumentF) U a
      (imaginary_input _ _ _ (GaussianGammaFiniteApproximantName.exponential_input _ _ ha))
  have hv : Γ ⊢[PRAAx] pointCN L v := multiply_fast constantF Product (ofGaussian z B) (sineData A B R)
    (constant_regular _) (GaussianSineProductName.name_regular _ _ _ hB hd)
  have hc := constant_regular (Γ := Γ) (negativeImaginary : PTm n)
  have multiplied := multiply_cross constantF constantF Si (multiplyF Pi L) _ _ _ _ hc hc si
    (multiply_fast Pi L x v hp hv) (cross_refl _ _ hc) exactSine
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ (rotated_sine A B R x hB hA))
    (cross_trans _ _ _ _ _ _ multiplied (rotated_product A B R x hB hA))

theorem actual_imaginary_sine_product_hyperbolic_sine_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 2) ⋏ (le one (var 1) ⋏ le (var 0) (var 2*var 1))) ⟶
        crossEquivalent sinhF productF (sinhData (var 0) (var 1) (var 2) (var 3)) (productData (var 0) (var 1) (var 2) (var 3))) :=
  closeUniv 4 (.impI (sinh_as_product _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianSineProductImaginaryHyperbolic
