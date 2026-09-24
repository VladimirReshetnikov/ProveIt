import Surreal.Algebra.OrdinaryRingMaps
import Surreal.Surcomplex.GaussianSmallTargets

/-!
# Explicit classification of omnific maps to small rings

The full `osq:cor:Oz` and `osq:cor:gaussian`: real nonunital maps are
parametrized by idempotents; Gaussian unital maps by roots of minus one.
The target may be noncommutative, and the Gaussian root need not be central.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Nonunital maps to small rings correspond to nonunital maps from the ordinary integers. -/
def omnificSmallNonUnitalHomEquiv (S : Type v) [NonUnitalRing S] [Small.{u} S] :
    (OmnificInteger.{u} →ₙ+* S) ≃ (ℤ →ₙ+* S) where
  toFun φ := φ.comp omnificIntCast.toNonUnitalRingHom
  invFun ψ := ψ.comp omnificConstantCoeff.toNonUnitalRingHom
  left_inv φ := by
    ext x
    exact (omnific_small_hom_eq_constant φ x).symm
  right_inv ψ := by
    ext n
    change ψ (omnificConstantCoeff (omnificIntCast n)) = ψ n
    rw [omnificConstantCoeff_intCast]

/-- Idempotents classify all nonunital maps from the real omnific ring to a small ring. -/
def omnificSmallHomIdempotentEquiv (S : Type v) [NonUnitalRing S] [Small.{u} S] :
    (OmnificInteger.{u} →ₙ+* S) ≃ {e : S // e * e = e} :=
  (omnificSmallNonUnitalHomEquiv S).trans (OrdinaryRingMaps.integerNonUnitalHomEquiv S)

/-- The parameter of a real nonunital map is its value at one. -/
theorem omnificSmallHomIdempotentEquiv_value {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : OmnificInteger.{u} →ₙ+* S) : (omnificSmallHomIdempotentEquiv S φ).val = φ 1 := by
  change φ (omnificIntCast 1) = φ 1
  rw [map_one]

/-- The explicit nonunital formula uses ordinary integer multiples of the image of one. -/
theorem omnific_small_hom_eq_zsmul {S : Type v} [NonUnitalRing S] [Small.{u} S]
    (φ : OmnificInteger.{u} →ₙ+* S) (x : OmnificInteger.{u}) :
    φ x = omnificConstantCoeff x • φ 1 := by
  rw [omnific_small_hom_eq_constant φ x]
  have he := map_zsmul (φ.comp omnificIntCast.toNonUnitalRingHom) (omnificConstantCoeff x) (1 : ℤ)
  change φ (omnificIntCast (omnificConstantCoeff x • (1 : ℤ))) =
    omnificConstantCoeff x • φ (omnificIntCast 1) at he
  simpa using he

/-- Exactly one unital map exists to each small unital ring. -/
theorem omnific_small_ringHom_unique (S : Type v) [Ring S] [Small.{u} S] :
    ∃! _φ : OmnificInteger.{u} →+* S, True := by
  refine ⟨(Int.castRingHom S).comp omnificConstantCoeff, trivial, ?_⟩
  intro φ _
  ext x
  exact omnific_small_ringHom_eq_constant φ x

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- All roots of minus one classify unital small-target Gaussian omnific maps. -/
def gaussianOmnificSmallHomRootEquiv (S : Type v) [Ring S] [Small.{u} S] :
    (GaussianOmnificInteger.{u} →+* S) ≃ {j : S // j ^ 2 = -1} :=
  (gaussianOmnificSmallRingHomEquiv S).trans (OrdinaryRingMaps.gaussianRingHomEquiv S)

/-- The root parameter is literally the image of the ordinary imaginary unit. -/
theorem gaussianOmnificSmallHomRootEquiv_value {S : Type v} [Ring S] [Small.{u} S]
    (φ : GaussianOmnificInteger.{u} →+* S) :
    (gaussianOmnificSmallHomRootEquiv S φ).val = φ gaussianOmnificI := rfl

/-- The source's explicit real-coordinate formula holds in every small unital ring target. -/
theorem gaussianOmnific_small_ringHom_coordinates {S : Type v} [Ring S] [Small.{u} S]
    (φ : GaussianOmnificInteger.{u} →+* S) (x : GaussianOmnificInteger.{u}) :
    φ x = (SignSequence.omnificConstantCoeff (gaussianOmnificRe x) : S) +
      (SignSequence.omnificConstantCoeff (gaussianOmnificIm x) : S) * φ gaussianOmnificI := by
  have hr := SignSequence.omnific_small_ringHom_eq_constant (φ.comp omnificToGaussian)
    (gaussianOmnificRe x)
  have hi := SignSequence.omnific_small_ringHom_eq_constant (φ.comp omnificToGaussian)
    (gaussianOmnificIm x)
  change φ (omnificToGaussian (gaussianOmnificRe x)) = _ at hr
  change φ (omnificToGaussian (gaussianOmnificIm x)) = _ at hi
  conv_lhs => rw [gaussianOmnific_coordinate_decomposition x, map_add, map_mul, hr, hi]

end
end Surreal.Surcomplex
