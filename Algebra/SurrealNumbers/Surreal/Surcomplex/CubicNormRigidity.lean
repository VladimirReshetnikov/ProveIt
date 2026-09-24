import Surreal.Algebra.CubicNormForm
import Surreal.Surcomplex.BinaryFormRigidity
import Surreal.Surcomplex.GaussianDecomposableFibers

/-!
# Actual omnific and Gaussian omnific cubic norm fibers

The displayed cubic example following `odg:thm:norm`, including its Gaussian
analogue. At nonzero ordinary levels, x³ + 2y³ + 4z³ - 6xyz has exactly
its ordinary integer or Gaussian integer solutions, respectively.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The cubic norm form at a nonzero complex level has constant support coordinates. -/
theorem nonnegativeSupport_cubic_norm_rigidity (c : ℂ) (hc : c ≠ 0)
    (x : Fin 3 → nonnegativeSupportSubring.{u})
    (hx : CubicNorm.value (x 0) (x 1) (x 2) = complexConstants c) :
    ∀ j, x j = complexConstants (constantCoeff (x j)) :=
  CubicNorm.coordinates_constant constantCoeffAlgHom nonnegativeSupport_unit_eq_constant c hc x hx

/-- Every actual omnific solution of the displayed cubic at a nonzero integer level is ordinary. -/
theorem omnific_cubic_norm_rigidity (c : ℤ) (hc : c ≠ 0)
    (x : Fin 3 → SignSequence.OmnificInteger.{u})
    (hx : CubicNorm.value (x 0) (x 1) (x 2) = SignSequence.omnificIntCast c) :
    ∀ j, x j = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff (x j)) := by
  have he := congrArg omnificSupportInclusion hx
  rw [CubicNorm.map_value, omnificSupportInclusion_intCast] at he
  have h := nonnegativeSupport_cubic_norm_rigidity (c : ℂ) (Int.cast_ne_zero.mpr hc)
    (fun j => omnificSupportInclusion (x j)) he
  intro j
  apply omnificSupportInclusion_injective
  rw [omnificSupportInclusion_intCast]
  simpa only [constantCoeff_omnificSupportInclusion] using h j

/-- Exact equality of the ordinary and omnific cubic norm fibers at nonzero integer levels. -/
theorem omnific_cubic_norm_solutions_iff (c : ℤ) (hc : c ≠ 0)
    (x : Fin 3 → SignSequence.OmnificInteger.{u}) :
    CubicNorm.value (x 0) (x 1) (x 2) = SignSequence.omnificIntCast c ↔
      ∃ a : Fin 3 → ℤ, CubicNorm.value (a 0) (a 1) (a 2) = c ∧
        ∀ j, x j = SignSequence.omnificIntCast (a j) := by
  constructor
  · intro hx
    refine ⟨fun j => SignSequence.omnificConstantCoeff (x j), ?_,
      omnific_cubic_norm_rigidity c hc x hx⟩
    simpa only [CubicNorm.map_value, SignSequence.omnificConstantCoeff_intCast] using
      congrArg SignSequence.omnificConstantCoeff hx
  · rintro ⟨a, ha, hx⟩
    simp only [hx, ← CubicNorm.map_value, ha]

/-- Every Gaussian omnific solution at a nonzero ordinary Gaussian level is ordinary Gaussian. -/
theorem gaussianOmnific_cubic_norm_rigidity (c : GaussianInt) (hc : c ≠ 0)
    (x : Fin 3 → GaussianOmnificInteger.{u})
    (hx : CubicNorm.value (x 0) (x 1) (x 2) = gaussianOmnificConstants c) :
    ∀ j, x j = gaussianOmnificConstants (gaussianOmnificConstantCoeff (x j)) := by
  have he := congrArg (fun a : GaussianOmnificInteger => a.val) hx
  change CubicNorm.value (x 0).val (x 1).val (x 2).val = (gaussianOmnificConstants c).val at he
  rw [gaussianOmnificConstants_val] at he
  have hc' : GaussianInt.toComplex c ≠ 0 := by
    intro h
    apply hc
    exact GaussianInt.toComplex_injective (by simpa using h)
  have h := nonnegativeSupport_cubic_norm_rigidity (GaussianInt.toComplex c) hc'
    (fun j => (x j).val) he
  intro j
  apply Subtype.ext
  rw [gaussianOmnificConstants_val, gaussianOmnificConstantCoeff_toComplex]
  exact h j

/-- Exact equality of the ordinary Gaussian and Gaussian omnific cubic norm fibers. -/
theorem gaussianOmnific_cubic_norm_solutions_iff (c : GaussianInt) (hc : c ≠ 0)
    (x : Fin 3 → GaussianOmnificInteger.{u}) :
    CubicNorm.value (x 0) (x 1) (x 2) = gaussianOmnificConstants c ↔
      ∃ a : Fin 3 → GaussianInt, CubicNorm.value (a 0) (a 1) (a 2) = c ∧
        ∀ j, x j = gaussianOmnificConstants (a j) := by
  constructor
  · intro hx
    refine ⟨fun j => gaussianOmnificConstantCoeff (x j), ?_,
      gaussianOmnific_cubic_norm_rigidity c hc x hx⟩
    simpa only [CubicNorm.map_value, gaussianOmnificConstantCoeff_constants] using
      congrArg gaussianOmnificConstantCoeff hx
  · rintro ⟨a, ha, hx⟩
    simp only [hx, ← CubicNorm.map_value, ha]

end
end Surreal.Surcomplex
