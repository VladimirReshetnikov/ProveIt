import Surreal.Algebra.QuadraticIdealDefinition
import Surreal.Algebra.QuadraticConstantObstruction
import Surreal.Surcomplex.GaussianOmnificIntegers
import Surreal.Foundations.OmnificIntegers

/-!
# A parameter-free quadratic definition of the actual purely infinite ideals

The actual omnific and Gaussian clauses of `odg:def:thm:ideal` and
`odg:def:eq:ideal`, together with `odg:def:cor:idealhom`. The displayed
predicate is literally ∃ y, x² = 2y² in the corresponding ring; it mentions
neither a coefficient map nor a square root nor an order.
-/

universe u v
namespace Surreal

noncomputable section

namespace Foundations.SignSequence

/-- The purely infinite omnific ideal is defined by one parameter-free quadratic witness. -/
theorem omnific_purelyInfinite_iff_quadratic (x : OmnificInteger.{u}) :
    x ∈ omnificPurelyInfiniteIdeal ↔ ∃ y : OmnificInteger.{u}, x ^ 2 = 2 * y ^ 2 := by
  letI : Algebra ℝ nonnegativeSupportSubring.{u} := realConstants.toAlgebra
  let ct : nonnegativeSupportSubring.{u} →ₐ[ℝ] ℝ :=
    { __ := constantCoeff
      commutes' := constantCoeff_realConstants }
  rw [show x ∈ omnificPurelyInfiniteIdeal ↔ constantCoeff x.val = 0 from
    CoefficientPullback.mem_ker_iff constantCoeff (Int.castRingHom ℝ) Int.cast_injective x]
  exact QuadraticIdeal.kernel_iff_quadratic ct (Int.castRingHom ℝ) Int.cast_injective
    2 (Real.sqrt 2) (by norm_num [Real.sq_sqrt])
    (Real.sqrt_ne_zero'.mpr (by norm_num)) QuadraticIdeal.integer_square_eq_two_zero
    (2 : OmnificInteger) (by
      change (2 : nonnegativeSupportSubring.{u}) = algebraMap ℝ nonnegativeSupportSubring.{u} ((Int.castRingHom ℝ) 2)
      simp only [map_ofNat]) x

/-- Every unital homomorphism of actual omnific rings preserves the purely infinite ideal. -/
theorem omnific_hom_preserves_purelyInfinite (φ : OmnificInteger.{u} →+* OmnificInteger.{v})
    (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal) :
    φ x ∈ omnificPurelyInfiniteIdeal :=
  (omnific_purelyInfinite_iff_quadratic _).mpr
    (QuadraticIdeal.map_quadratic_witness φ x ((omnific_purelyInfinite_iff_quadratic x).mp hx))

end Foundations.SignSequence
namespace Surcomplex

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The Gaussian constant-term kernel has the same parameter-free quadratic definition. -/
theorem gaussianOmnific_purelyInfinite_iff_quadratic (x : GaussianOmnificInteger.{u}) :
    x ∈ RingHom.ker (gaussianOmnificConstantCoeff.{u}) ↔
      ∃ y : GaussianOmnificInteger.{u}, x ^ 2 = 2 * y ^ 2 := by
  rw [show x ∈ RingHom.ker (gaussianOmnificConstantCoeff.{u}) ↔ constantCoeff x.val = 0 from
    CoefficientPullback.mem_ker_iff constantCoeff GaussianInt.toComplex
      GaussianInt.toComplex_injective x]
  apply QuadraticIdeal.kernel_iff_quadratic constantCoeffAlgHom GaussianInt.toComplex
    GaussianInt.toComplex_injective 2 (Real.sqrt 2 : ℂ)
  · have h : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
      exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
    simpa only [map_ofNat] using h
  · exact Complex.ofReal_ne_zero.mpr (Real.sqrt_ne_zero'.mpr (by norm_num))
  · exact QuadraticIdeal.gaussian_square_eq_two_zero
  · change (2 : nonnegativeSupportSubring.{u}) = algebraMap ℂ nonnegativeSupportSubring.{u} (GaussianInt.toComplex 2)
    simp only [map_ofNat]

/-- Every unital homomorphism of Gaussian omnific rings preserves the purely infinite ideal. -/
theorem gaussianOmnific_hom_preserves_purelyInfinite
    (φ : GaussianOmnificInteger.{u} →+* GaussianOmnificInteger.{v})
    (x : GaussianOmnificInteger.{u}) (hx : x ∈ RingHom.ker (gaussianOmnificConstantCoeff.{u})) :
    φ x ∈ RingHom.ker (gaussianOmnificConstantCoeff.{v}) :=
  (gaussianOmnific_purelyInfinite_iff_quadratic _).mpr
    (QuadraticIdeal.map_quadratic_witness φ x
      ((gaussianOmnific_purelyInfinite_iff_quadratic x).mp hx))

end Surcomplex
end
end Surreal
