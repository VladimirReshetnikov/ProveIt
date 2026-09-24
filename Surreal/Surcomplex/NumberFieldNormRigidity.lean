import Surreal.Algebra.SeparableNormRigidity
import Surreal.Algebra.IntegralNormCoefficients
import Surreal.Surcomplex.BinaryFormRigidity
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Actual omnific rigidity for number-field norm forms

The rigidity assertion of `odg:thm:norm`. The determinant norm polynomial
is defined over Q and evaluated in the actual surreal field, so there is
no assumption that the number field embeds in the surreals. Complex
coefficient extension and the proved independent embedding forms force
all omnific coordinates to be ordinary integers.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Module

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

variable {L ι : Type*} [Field L] [Algebra ℚ L] [Module.Finite ℚ L]
  [Fintype ι] [DecidableEq ι]

/-- A number-field norm form has constant complex support coordinates at every nonzero
ordinary complex level. -/
theorem nonnegativeSupport_numberField_norm_rigidity (b : Basis ι ℚ L)
    (c : ℂ) (hc : c ≠ 0) (x : ι → nonnegativeSupportSubring.{u})
    (hx : (NormForm.polynomial b).eval₂ (complexConstants.comp (algebraMap ℚ ℂ)) x =
      complexConstants c) :
    ∀ j, x j = complexConstants (constantCoeff (x j)) :=
  NormForm.coordinates_constant constantCoeffAlgHom nonnegativeSupport_unit_eq_constant
    b c hc x hx

/-- An actual omnific solution of a number-field norm form at a nonzero rational level has
ordinary integer coordinates. The equation is the literal rational-polynomial evaluation
in the actual surreal field. -/
theorem omnific_numberField_norm_rigidity (b : Basis ι ℚ L) (c : ℚ) (hc : c ≠ 0)
    (x : ι → SignSequence.OmnificInteger.{u})
    (hx : (NormForm.polynomial b).eval₂ (algebraMap ℚ SignSequence)
      (fun j => SignSequence.omnificToSurreal (x j)) = (c : SignSequence)) :
    ∀ j, x j = SignSequence.omnificIntCast (SignSequence.omnificConstantCoeff (x j)) := by
  let φ := complexConstants.comp (algebraMap ℚ ℂ)
  have he : (NormForm.polynomial b).eval₂ φ (fun j => omnificSupportInclusion (x j)) =
      complexConstants (c : ℂ) := by
    apply Subtype.ext
    change nonnegativeSupportSubring.subtype
      ((NormForm.polynomial b).eval₂ φ (fun j => omnificSupportInclusion (x j))) = _
    rw [MvPolynomial.hom_eval₂]
    have hφ : nonnegativeSupportSubring.subtype.comp φ =
        ofReal.comp (algebraMap ℚ SignSequence) := Subsingleton.elim _ _
    rw [hφ]
    have h := congrArg ofReal hx
    rw [MvPolynomial.hom_eval₂] at h
    change (NormForm.polynomial b).eval₂ (ofReal.comp (algebraMap ℚ SignSequence))
      (fun j => ofReal (SignSequence.omnificToSurreal (x j))) = ofComplex (c : ℂ)
    simpa only [map_ratCast] using h
  have h := nonnegativeSupport_numberField_norm_rigidity b (c : ℂ)
    (Rat.cast_ne_zero.mpr hc) (fun j => omnificSupportInclusion (x j)) he
  intro j
  apply omnificSupportInclusion_injective
  rw [omnificSupportInclusion_intCast]
  simpa only [constantCoeff_omnificSupportInclusion] using h j

/-- A native integer polynomial representing the norm has exactly its ordinary integer
solutions at every nonzero integer level. -/
theorem omnific_integer_norm_solutions_iff (b : Basis ι ℚ L)
    (P : MvPolynomial ι ℤ) (hP : P.map (Int.castRingHom ℚ) = NormForm.polynomial b)
    (c : ℤ) (hc : c ≠ 0) (x : ι → SignSequence.OmnificInteger.{u}) :
    P.eval₂ SignSequence.omnificIntCast x = SignSequence.omnificIntCast c ↔
      ∃ a : ι → ℤ, P.eval a = c ∧ ∀ j, x j = SignSequence.omnificIntCast (a j) := by
  constructor
  · intro hx
    have he : (NormForm.polynomial b).eval₂ (algebraMap ℚ SignSequence)
        (fun j => SignSequence.omnificToSurreal (x j)) = ((c : ℚ) : SignSequence) := by
      rw [← hP, MvPolynomial.eval₂_map]
      have hm := congrArg SignSequence.omnificToSurreal hx
      rw [MvPolynomial.hom_eval₂, SignSequence.omnificToSurreal_intCast] at hm
      have hf : (algebraMap ℚ SignSequence.{u}).comp (Int.castRingHom ℚ) =
          SignSequence.omnificToSurreal.comp SignSequence.omnificIntCast := Subsingleton.elim _ _
      rw [hf, Rat.cast_intCast]
      exact hm
    have h := omnific_numberField_norm_rigidity b (c : ℚ) (Int.cast_ne_zero.mpr hc) x he
    refine ⟨fun j => SignSequence.omnificConstantCoeff (x j), ?_, h⟩
    have hm := congrArg SignSequence.omnificConstantCoeff hx
    rw [SignSequence.omnificConstantCoeff_eval, SignSequence.omnificConstantCoeff_intCast] at hm
    exact hm
  · rintro ⟨a, ha, hx⟩
    have he : x = SignSequence.omnificIntCast ∘ a := funext hx
    rw [he, ← MvPolynomial.eval₂_comp, ha]

/-- Every rational basis of algebraic integers supplies an integer norm polynomial with
the full actual omnific solution-set rigidity property. -/
theorem exists_integer_norm_with_rigidity (b : Basis ι ℚ L) (hb : ∀ j, IsIntegral ℤ (b j)) :
    ∃ P : MvPolynomial ι ℤ, P.map (Int.castRingHom ℚ) = NormForm.polynomial b ∧
      ∀ (c : ℤ), c ≠ 0 → ∀ x : ι → SignSequence.OmnificInteger.{u},
        P.eval₂ SignSequence.omnificIntCast x = SignSequence.omnificIntCast c ↔
          ∃ a : ι → ℤ, P.eval a = c ∧ ∀ j, x j = SignSequence.omnificIntCast (a j) := by
  obtain ⟨P, hP⟩ := NormForm.exists_integer_polynomial b hb
  exact ⟨P, hP, fun c hc x => omnific_integer_norm_solutions_iff b P hP c hc x⟩

end
end Surreal.Surcomplex
