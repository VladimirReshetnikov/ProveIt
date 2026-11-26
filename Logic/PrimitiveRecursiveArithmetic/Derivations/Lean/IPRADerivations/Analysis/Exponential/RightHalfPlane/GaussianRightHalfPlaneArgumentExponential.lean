import IPRADerivations.Analysis.RationalArithmetic.Complex.GaussianRightHalfPlaneArgumentAxis
import IPRADerivations.Analysis.Names.GaussianNamedHalf

/-!
# Exponentiation in the two right half-plane argument charts

The square of the small-angle exponential is the literal rational
Cayley value. The large-angle exponential is the imaginary unit
times the conjugate of the small-angle exponential at the reciprocal.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentExponential

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ComplexLogarithmRemainder (oneCode scale)
open GaussianArctangentQuarterExponential (quarterF)
open GaussianArctangentCayleyValues (imaginaryPoint value)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaAdjacentCutoff (multiply_cross)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianImaginaryNameConjugation (imaginarySamples)
open GaussianNameArithmetic (addF addData add_equivalent add_fast multiplyF multiplyData)
open GaussianNameEquivalence (crossEquivalent cross_trans cross_symm cross_to_diagonal)
open GaussianNameRingLaws (negativeF negativeData)
open GaussianRadiusExponentialName (input)
open GaussianRationalHorner (ofGaussian ofGaussian_canonical ofGaussian_represents
  canonical_unique represents_congr)
open GaussianRightHalfPlaneArgument (smallF smallData small_input small_regular small_bound
  half_bounded largeF largeData radius)
open GaussianRightHalfPlaneArgumentAxis (small_axis)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "atanF" => GaussianArctangentPartialQuadrature.nameF
local notation "atData" => GaussianArctangentPartialQuadrature.data
local notation "E" => GaussianRadiusExponentialName.nameF
local notation "ed" => GaussianRadiusExponentialName.data
local notation "hpoint" => GaussianRightHalfPlaneArgument.half
local notation "rhalf" => GaussianEulerSquareFactorInverse.half
local notation "xp" => GaussianNameConjugation.nameF

def smallExpData (A B : PTm n) : PTm n := ed two (smallData A B)
def squareData (A B : PTm n) : PTm n :=
  multiplyData (E smallF) (E smallF) (smallExpData A B) (smallExpData A B)

private theorem half_literal : Γ ⊢[PRAAx] (hpoint : PTm n) ≐ rhalf := by
  have h : Γ ⊢[PRAAx] le one two := le_succ_self one
  have e : Γ ⊢[PRAAx] GaussianRootAlgebra.equal oneCode (scale one oneCode) := by
    apply GaussianRootAlgebra.equal_of_values <;>
      simp only [GaussianRootAlgebra.re_scale,GaussianRootAlgebra.im_scale,
        GaussianRootAlgebra.re_one,GaussianRootAlgebra.im_one] <;> ipra_simps <;> ring
  exact canonical_unique _ _ _ two (ofGaussian_canonical _ _ h) (ofGaussian_canonical _ _ h) h
    (represents_congr (.eqRefl _) e (.eqRefl _) (ofGaussian_represents _ _ h)) (ofGaussian_represents _ _ h)

private theorem small_ordinary (A B : PTm n) (h : Γ ⊢[PRAAx] pointCN atanF (atData B A)) :
    Γ ⊢[PRAAx] crossEquivalent smallF (GaussianNamedHalf.nameF atanF)
      (smallData A B) (GaussianNamedHalf.data atanF (atData B A)) := by
  have same := GaussianBoundedConstantProductName.ordinary_product_identity atanF one hpoint (atData B A)
    (.andI h half_bounded)
  have adjust := multiply_cross constantF constantF atanF atanF hpoint rhalf (atData B A) (atData B A)
    (constant_regular _) (constant_regular _) h h
    (GaussianArctangentExponentialPeriod.constant_cross_congr _ _ half_literal)
    (GaussianNameEquivalence.cross_refl _ _ h)
  exact cross_trans _ _ _ _ _ _ same adjust

theorem small_double (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] crossEquivalent (addF smallF smallF) atanF
      (addData (smallData A B) (smallData A B)) (atData B A) := by
  let x := smallData A B
  let y := atData B A
  let H := GaussianNamedHalf.nameF atanF
  let z := GaussianNamedHalf.data atanF y
  have a := GaussianArctangentPartialQuadrature.name_regular B A hA hB
  have o := cross_to_diagonal _ _ _ _ (small_ordinary A B a)
  have s := small_regular A B hA hB
  have r := GaussianNamedHalf.regular atanF y a
  have e := add_equivalent smallF H smallF H x z x z s r s r o o
  exact cross_trans _ _ _ _ _ _ e (GaussianNamedHalf.double atanF y a)

theorem small_square (A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le B A) :
    Γ ⊢[PRAAx] crossEquivalent (multiplyF (E smallF) (E smallF)) constantF (squareData A B) (value A B) := by
  let x := smallData A B
  have s := small_input A B hA hB
  have sum := GaussianExponentialAddition.exponential_add_cross smallF smallF two x x (le_succ_self one) s s
  have exp := GaussianExponentialRadiusIndependence.independent_radii_proper _ _ (two+two) two _ _
    (GaussianExponentialReference.add_input _ _ two x x s s)
    (GaussianArctangentPartialExponential.exponential_input B A hA hB) (small_double A B hA hB)
  exact cross_trans _ _ _ _ _ _ sum
    (cross_trans _ _ _ _ _ _ exp (GaussianArctangentPartialExponential.exponential_cross B A hA hB))

private theorem small_imaginary (A B : PTm n) : Γ ⊢[PRAAx] imaginarySamples smallF (smallData A B) := by
  refine .allI ?_
  simpa only [imaginarySamples,GaussianRightHalfPlaneArgument.subst_smallData,Syn.shift] using
    small_axis (var 0) (Syn.shift A) (Syn.shift B)

theorem large_exponential (A B : PTm n) (hA : Γ ⊢[PRAAx] le A B) (hB : Γ ⊢[PRAAx] le one B) :
    Γ ⊢[PRAAx] crossEquivalent (E largeF) (multiplyF constantF (xp (E smallF)))
      (ed radius (largeData A B))
      (multiplyData constantF (xp (E smallF)) imaginaryPoint (smallExpData B A)) := by
  let x := smallData B A
  let Q := E quarterF
  let N := E (negativeF smallF)
  let S := xp (E smallF)
  have small := small_input B A hB hA
  have hq := GaussianArctangentQuarterExponential.quarter_input (Γ := Γ) zero
    (GaussianArctangentQuarterExponential.original_bounded_arguments zero)
  have hn := GaussianExponentialInverse.negative_input smallF two x small
  have add := GaussianExponentialAddition.exponential_add_cross quarterF (negativeF smallF) two zero (negativeData x)
    (le_succ_self one) hq hn
  have e := GaussianImaginaryNameConjugation.negative_exponential_conjugate_cross smallF two x small
    (small_imaginary B A)
  have product := multiply_cross Q constantF N S (ed two zero) imaginaryPoint (ed two (negativeData x)) (ed two x)
    (GaussianRadiusExponentialName.name_regular _ _ _ hq) (constant_regular _)
    (GaussianRadiusExponentialName.name_regular _ _ _ hn)
    (GaussianNameConjugation.regular _ _ (GaussianRadiusExponentialName.name_regular _ _ _ small))
    (GaussianArctangentOriginalExponential.quarter_cross zero) e
  exact cross_trans _ _ _ _ _ _ (cross_symm _ _ _ _ add) product

theorem actual_right_half_plane_small_argument_exponential_square_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((le one (var 0) ⋏ le (var 1) (var 0)) ⟶ crossEquivalent (multiplyF (E smallF) (E smallF))
        constantF (squareData (var 0) (var 1)) (value (var 0) (var 1))) :=
  closeUniv 2 (.impI (small_square _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

theorem actual_right_half_plane_large_argument_exponential_reciprocal_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      ((le (var 0) (var 1) ⋏ le one (var 1)) ⟶
        crossEquivalent (E largeF) (multiplyF constantF (xp (E smallF))) (ed radius (largeData (var 0) (var 1)))
          (multiplyData constantF (xp (E smallF)) imaginaryPoint (smallExpData (var 1) (var 0)))) :=
  closeUniv 2 (.impI (large_exponential _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianRightHalfPlaneArgumentExponential
