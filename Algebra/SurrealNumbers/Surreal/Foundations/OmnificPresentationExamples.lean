import Surreal.Foundations.OmnificSmallTargets
import Mathlib.RingTheory.AdjoinRoot

/-!
# Polynomial points that lose infinite coefficients

The examples following `osq:thm:presentations`. The native AdjoinRoot
presentation Oz[T]/(T squared minus omega) has exactly square-zero images
for its generator in small commutative targets, while its actual omnific
root gives a nonzero class-valued image. The reciprocal relation has no
small unital solution but has an explicit solution in the surreal field.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- The relation T squared equals omega in the presentation example. -/
def omnificOmegaRootPolynomial : Polynomial OmnificInteger.{u} :=
  Polynomial.X ^ 2 - Polynomial.C (omnificMonomial 1 zero_lt_one)

/-- Coefficient extraction turns the defining relation into T squared. -/
theorem omnificOmegaRootPolynomial_map :
    omnificOmegaRootPolynomial.{u}.map omnificConstantCoeff = Polynomial.X ^ 2 := by
  have hw : omnificConstantCoeff (omnificMonomial (1 : SignSequence.{u}) zero_lt_one) = 0 :=
    omnificMonomial_mem_purelyInfinite _ _
  rw [omnificOmegaRootPolynomial, Polynomial.map_sub, Polynomial.map_pow, Polynomial.map_X,
    Polynomial.map_C, hw, Polynomial.C_0, sub_zero]

/-- The native ring Oz[T]/(T squared minus omega). -/
abbrev OmnificOmegaRootAlgebra := AdjoinRoot omnificOmegaRootPolynomial.{u}

/-- The universal generator satisfies the defining quadratic relation. -/
theorem omnificOmegaRootAlgebra_root_sq :
    (AdjoinRoot.root omnificOmegaRootPolynomial.{u}) ^ 2 =
      AdjoinRoot.of omnificOmegaRootPolynomial (omnificMonomial 1 zero_lt_one) := by
  have h := AdjoinRoot.eval₂_root omnificOmegaRootPolynomial.{u}
  change (Polynomial.X ^ 2 - Polynomial.C (omnificMonomial 1 zero_lt_one)).eval₂
    (AdjoinRoot.of omnificOmegaRootPolynomial.{u}) (AdjoinRoot.root omnificOmegaRootPolynomial) = 0 at h
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_C,
    sub_eq_zero] at h
  exact h

/-- A square-zero element defines a unital map from the actual presented ring. -/
def omnificOmegaRootMap {B : Type v} [CommRing B] (j : B) (hj : j ^ 2 = 0) :
    OmnificOmegaRootAlgebra.{u} →+* B :=
  AdjoinRoot.lift ((Int.castRingHom B).comp omnificConstantCoeff) j (by
    have hw : omnificConstantCoeff (omnificMonomial (1 : SignSequence.{u}) zero_lt_one) = 0 :=
      omnificMonomial_mem_purelyInfinite _ _
    simp only [omnificOmegaRootPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.comp_apply, hw, map_zero, hj, sub_self])

/-- Every small-ring image of the generator is square-zero. -/
theorem omnificOmegaRootAlgebra_small_root_sq {B : Type v} [Ring B] [Small.{u} B]
    (φ : OmnificOmegaRootAlgebra.{u} →+* B) :
    (φ (AdjoinRoot.root omnificOmegaRootPolynomial)) ^ 2 = 0 := by
  rw [← map_pow, omnificOmegaRootAlgebra_root_sq]
  exact omnific_small_hom_purelyInfinite
    (φ.comp (AdjoinRoot.of omnificOmegaRootPolynomial)).toNonUnitalRingHom _
    (omnificMonomial_mem_purelyInfinite _ _)

/-- Small commutative target maps correspond exactly to their square-zero generator image. -/
def omnificOmegaRootSmallHomEquiv (B : Type v) [CommRing B] [Small.{u} B] :
    (OmnificOmegaRootAlgebra.{u} →+* B) ≃ {j : B // j ^ 2 = 0} where
  toFun φ := ⟨φ (AdjoinRoot.root omnificOmegaRootPolynomial), omnificOmegaRootAlgebra_small_root_sq φ⟩
  invFun j := omnificOmegaRootMap j.val j.property
  left_inv φ := by
    apply AdjoinRoot.ringHom_ext
    · change (AdjoinRoot.lift _ _ _).comp _ = _
      rw [AdjoinRoot.lift_comp_of]
      apply RingHom.ext
      intro a
      exact (omnific_small_ringHom_eq_constant (φ.comp (AdjoinRoot.of omnificOmegaRootPolynomial)) a).symm
    · exact AdjoinRoot.lift_root _
  right_inv j := Subtype.ext (AdjoinRoot.lift_root _)

/-- Every small field image kills the universal quadratic generator. -/
theorem omnificOmegaRootAlgebra_small_field_root {B : Type v} [Field B] [Small.{u} B]
    (φ : OmnificOmegaRootAlgebra.{u} →+* B) : φ (AdjoinRoot.root omnificOmegaRootPolynomial) = 0 :=
  eq_zero_of_pow_eq_zero (omnificOmegaRootAlgebra_small_root_sq φ)

/-- The positive half-exponent monomial is an actual omnific square root of omega. -/
theorem omnific_half_monomial_sq :
    omnificMonomial (1 / 2 : SignSequence.{u}) (by norm_num) ^ 2 =
      omnificMonomial 1 zero_lt_one := by
  apply omnificToSurreal_injective
  rw [map_pow, omnificToSurreal_monomial, omnificToSurreal_monomial,
    pow_two, ← omegaPower_add]
  norm_num

/-- The actual nonzero omnific root gives a class-valued solution outside small-target collapse. -/
def omnificOmegaRootActualMap : OmnificOmegaRootAlgebra.{u} →+* OmnificInteger.{u} :=
  AdjoinRoot.lift (RingHom.id _) (omnificMonomial (1 / 2) (by norm_num)) (by
    simp only [omnificOmegaRootPolynomial, Polynomial.eval₂_sub, Polynomial.eval₂_pow,
      Polynomial.eval₂_X, Polynomial.eval₂_C, RingHom.id_apply, omnific_half_monomial_sq, sub_self])

/-- This class-valued map sends the universal generator to a nonzero element. -/
theorem omnificOmegaRootActualMap_root_ne_zero :
    omnificOmegaRootActualMap.{u} (AdjoinRoot.root omnificOmegaRootPolynomial) ≠ 0 := by
  rw [omnificOmegaRootActualMap, AdjoinRoot.lift_root]
  exact omnificMonomial_ne_zero _ _

/-- The equation omega times T equals one is impossible under every small unital representation. -/
theorem omnific_omega_mul_ne_one_small {B : Type v} [Ring B] [Nontrivial B] [Small.{u} B]
    (φ : OmnificInteger.{u} →+* B) (t : B) : φ (omnificMonomial 1 zero_lt_one) * t ≠ 1 := by
  have he := omnific_small_hom_purelyInfinite φ.toNonUnitalRingHom _
    (omnificMonomial_mem_purelyInfinite (1 : SignSequence.{u}) zero_lt_one)
  change φ (omnificMonomial 1 zero_lt_one) = 0 at he
  simp [he]

/-- The same reciprocal equation has a solution in the actual surreal field. -/
theorem surreal_omega_reciprocal_solution :
    omegaPower (1 : SignSequence.{u}) * (omegaPower 1)⁻¹ = 1 :=
  mul_inv_cancel₀ (omegaPower_ne_zero 1)

end
end Surreal.Foundations.SignSequence
