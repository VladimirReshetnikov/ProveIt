import Surreal.Algebra.GaussianNonUnitalMaps
import Surreal.Surcomplex.OmnificMapClassification

/-!
# Classification of nonunital Gaussian omnific observations

The unnumbered consequence following `osq:cor:gaussian`. Maps into any
small nonunital ring correspond to compatible pairs (e,j), with exactly
the relations ee=e, ej=je=j and jj=-e. Neither element need be central.
-/

universe u v
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- The universal constant-term factorization as an equivalence of nonunital map types. -/
def gaussianOmnificSmallNonUnitalHomEquiv (S : Type v) [NonUnitalRing S] [Small.{u} S] :
    (GaussianOmnificInteger.{u} →ₙ+* S) ≃ (GaussianInt →ₙ+* S) where
  toFun φ := φ.comp gaussianOmnificConstants.{u}.toNonUnitalRingHom
  invFun ψ := ψ.comp gaussianOmnificConstantCoeff.{u}.toNonUnitalRingHom
  left_inv φ := by
    ext x
    exact (gaussianOmnific_small_hom_eq_constant φ x).symm
  right_inv ψ := by
    ext d
    change ψ (gaussianOmnificConstantCoeff.{u} (gaussianOmnificConstants.{u} d)) = ψ d
    rw [gaussianOmnificConstantCoeff_constants]

/-- Compatible idempotent/imaginary pairs classify all small-target nonunital Gaussian maps. -/
def gaussianOmnificSmallHomPairEquiv (S : Type v) [NonUnitalRing S] [Small.{u} S] :
    (GaussianOmnificInteger.{u} →ₙ+* S) ≃ OrdinaryRingMaps.GaussianPair S :=
  (gaussianOmnificSmallNonUnitalHomEquiv S).trans (OrdinaryRingMaps.gaussianNonUnitalHomEquiv S)

/-- The first parameter is literally the image of one. -/
theorem gaussianOmnificSmallHomPairEquiv_one {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : GaussianOmnificInteger.{u} →ₙ+* S) :
    (gaussianOmnificSmallHomPairEquiv S φ).val.1 = φ 1 := by
  change φ (gaussianOmnificConstants.{u} 1) = φ 1
  rw [map_one]

/-- The second parameter is literally the image of the ordinary imaginary unit. -/
theorem gaussianOmnificSmallHomPairEquiv_I {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : GaussianOmnificInteger.{u} →ₙ+* S) :
    (gaussianOmnificSmallHomPairEquiv S φ).val.2 = φ gaussianOmnificI := rfl

/-- Every nonunital Gaussian omnific map discards all infinite coefficients in both coordinates. -/
theorem gaussianOmnific_small_nonunital_coordinates {S : Type v}
    [NonUnitalRing S] [Small.{u} S] (φ : GaussianOmnificInteger.{u} →ₙ+* S)
    (x : GaussianOmnificInteger.{u}) :
    φ x = SignSequence.omnificConstantCoeff (gaussianOmnificRe x) • φ 1 +
      SignSequence.omnificConstantCoeff (gaussianOmnificIm x) • φ gaussianOmnificI := by
  have hr := SignSequence.omnific_small_hom_eq_zsmul
    (φ.comp omnificToGaussian.toNonUnitalRingHom) (gaussianOmnificRe x)
  have hi := SignSequence.omnific_small_hom_eq_zsmul
    (φ.comp omnificToGaussian.toNonUnitalRingHom) (gaussianOmnificIm x)
  change φ (omnificToGaussian (gaussianOmnificRe x)) =
    SignSequence.omnificConstantCoeff (gaussianOmnificRe x) • φ (omnificToGaussian 1) at hr
  change φ (omnificToGaussian (gaussianOmnificIm x)) =
    SignSequence.omnificConstantCoeff (gaussianOmnificIm x) • φ (omnificToGaussian 1) at hi
  rw [map_one] at hr hi
  have he : φ 1 * φ gaussianOmnificI = φ gaussianOmnificI := by rw [← map_mul, one_mul]
  conv_lhs => rw [gaussianOmnific_coordinate_decomposition x, map_add, map_mul, hr, hi]
  rw [smul_mul_assoc, he]

/-- The inverse equivalence evaluates Gaussian constant coordinates at the chosen pair. -/
theorem gaussianOmnificSmallHomPairEquiv_symm_apply {S : Type v}
    [NonUnitalRing S] [Small.{u} S] (p : OrdinaryRingMaps.GaussianPair S)
    (x : GaussianOmnificInteger.{u}) :
    (gaussianOmnificSmallHomPairEquiv S).symm p x =
      (gaussianOmnificConstantCoeff.{u} x).re • p.val.1 +
        (gaussianOmnificConstantCoeff.{u} x).im • p.val.2 := rfl

/-- A nonunital map into a unital target preserves one exactly when its first parameter is one. -/
theorem gaussianOmnificSmallHomPairEquiv_unital_iff {S : Type v}
    [Ring S] [Small.{u} S] (φ : GaussianOmnificInteger.{u} →ₙ+* S) :
    φ 1 = 1 ↔ (gaussianOmnificSmallHomPairEquiv S φ).val.1 = 1 := by
  rw [gaussianOmnificSmallHomPairEquiv_one]

end
end Surreal.Surcomplex
