import Surreal.Algebra.ProductNormRigidity
import Surreal.Surcomplex.NumberFieldNormRigidity
import Surreal.Surcomplex.GaussianOmnificIntegers

/-!
# Finite étale norm rigidity for actual omnific rings

The actual-ring clauses (a) and (b) of `odg:dec:thm:etale`. Finite étale
algebras are represented by finite products of finite field extensions.
The basis is arbitrary. Gaussian rigidity permits any characteristic-zero
base field embedded in C, including Q and Q(i). The equations evaluate the
native norm polynomial in the actual surreal or surcomplex field.
-/

universe u
namespace Surreal.Surcomplex

open Foundations Module

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

variable {H J : Type*} [Fintype H] [DecidableEq H] [Fintype J] [DecidableEq J]

/-- Finite étale norm equations over a complex coefficient field have constant support coordinates. -/
theorem nonnegativeSupport_etale_norm_rigidity {K : Type*} [Field K] [CharZero K]
    [Algebra K ℂ] {L : H → Type*} [∀ h, Field (L h)] [∀ h, Algebra K (L h)]
    [∀ h, Module.Finite K (L h)] (b : Basis J K (∀ h, L h))
    (c : ℂ) (hc : c ≠ 0) (x : J → nonnegativeSupportSubring.{u})
    (hx : (NormForm.polynomial b).eval₂ (complexConstants.comp (algebraMap K ℂ)) x =
      complexConstants c) :
    ∀ j, x j = complexConstants (constantCoeff (x j)) :=
  NormForm.etale_coordinates_constant constantCoeffAlgHom nonnegativeSupport_unit_eq_constant
    b c hc x hx

section Rational

variable {L : H → Type*} [∀ h, Field (L h)] [∀ h, Algebra ℚ (L h)]
  [∀ h, Module.Finite ℚ (L h)]

/-- An actual omnific solution of a finite étale norm form at a nonzero rational level has
ordinary integer coordinates. The equation is the literal rational-polynomial evaluation
in the actual surreal field. -/
theorem omnific_etale_norm_rigidity (b : Basis J ℚ (∀ h, L h)) (c : ℚ) (hc : c ≠ 0)
    (x : J → SignSequence.OmnificInteger.{u})
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
  have h := nonnegativeSupport_etale_norm_rigidity b (c : ℂ)
    (Rat.cast_ne_zero.mpr hc) (fun j => omnificSupportInclusion (x j)) he
  intro j
  apply omnificSupportInclusion_injective
  rw [omnificSupportInclusion_intCast]
  simpa only [constantCoeff_omnificSupportInclusion] using h j

/-- A native integer polynomial representing the norm has exactly its ordinary integer
solutions at every nonzero integer level. -/
theorem omnific_integer_etale_norm_solutions_iff (b : Basis J ℚ (∀ h, L h))
    (P : MvPolynomial J ℤ) (hP : P.map (Int.castRingHom ℚ) = NormForm.polynomial b)
    (c : ℤ) (hc : c ≠ 0) (x : J → SignSequence.OmnificInteger.{u}) :
    P.eval₂ SignSequence.omnificIntCast x = SignSequence.omnificIntCast c ↔
      ∃ a : J → ℤ, P.eval a = c ∧ ∀ j, x j = SignSequence.omnificIntCast (a j) := by
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
    have h := omnific_etale_norm_rigidity b (c : ℚ) (Int.cast_ne_zero.mpr hc) x he
    refine ⟨fun j => SignSequence.omnificConstantCoeff (x j), ?_, h⟩
    have hm := congrArg SignSequence.omnificConstantCoeff hx
    rw [SignSequence.omnificConstantCoeff_eval, SignSequence.omnificConstantCoeff_intCast] at hm
    exact hm
  · rintro ⟨a, ha, hx⟩
    have he : x = SignSequence.omnificIntCast ∘ a := funext hx
    rw [he, ← MvPolynomial.eval₂_comp, ha]

end Rational

/-- At a nonzero ordinary complex level, a finite étale norm equation over any complex
coefficient field has only ordinary Gaussian solutions among Gaussian omnific tuples. -/
theorem gaussianOmnific_etale_norm_rigidity {K : Type*} [Field K] [CharZero K]
    [Algebra K ℂ] {L : H → Type*} [∀ h, Field (L h)] [∀ h, Algebra K (L h)]
    [∀ h, Module.Finite K (L h)] (b : Basis J K (∀ h, L h))
    (c : ℂ) (hc : c ≠ 0) (x : J → GaussianOmnificInteger.{u})
    (hx : (NormForm.polynomial b).eval₂ (ofComplex.comp (algebraMap K ℂ))
      (fun j => gaussianOmnificToSurcomplex (x j)) = ofComplex c) :
    ∀ j, x j = gaussianOmnificConstants (gaussianOmnificConstantCoeff (x j)) := by
  have he : (NormForm.polynomial b).eval₂ (complexConstants.comp (algebraMap K ℂ))
      (fun j => (x j).val) = complexConstants c := by
    apply Subtype.ext
    change nonnegativeSupportSubring.subtype
      ((NormForm.polynomial b).eval₂ (complexConstants.comp (algebraMap K ℂ))
        (fun j => (x j).val)) = ofComplex c
    rw [MvPolynomial.hom_eval₂]
    exact hx
  have h := nonnegativeSupport_etale_norm_rigidity b c hc (fun j => (x j).val) he
  intro j
  apply Subtype.ext
  rw [gaussianOmnificConstants_val, gaussianOmnificConstantCoeff_toComplex]
  exact h j

/-- Gaussian omnific fibers of finite étale norm equations are precisely their ordinary
Gaussian fibers, with coefficients evaluated in the ordinary complex field. -/
theorem gaussianOmnific_etale_norm_solutions_iff {K : Type*} [Field K] [CharZero K]
    [Algebra K ℂ] {L : H → Type*} [∀ h, Field (L h)] [∀ h, Algebra K (L h)]
    [∀ h, Module.Finite K (L h)] (b : Basis J K (∀ h, L h))
    (c : ℂ) (hc : c ≠ 0) (x : J → GaussianOmnificInteger.{u}) :
    (NormForm.polynomial b).eval₂ (ofComplex.comp (algebraMap K ℂ))
      (fun j => gaussianOmnificToSurcomplex (x j)) = ofComplex c ↔
      ∃ a : J → GaussianInt,
        (NormForm.polynomial b).eval₂ (algebraMap K ℂ) (fun j => GaussianInt.toComplex (a j)) = c ∧
        ∀ j, x j = gaussianOmnificConstants (a j) := by
  have hv (a : GaussianInt) : gaussianOmnificToSurcomplex (gaussianOmnificConstants.{u} a) =
      ofComplex (GaussianInt.toComplex a) := rfl
  constructor
  · intro hx
    have h := gaussianOmnific_etale_norm_rigidity b c hc x hx
    refine ⟨fun j => gaussianOmnificConstantCoeff (x j), ?_, h⟩
    apply ofComplex_injective
    rw [MvPolynomial.hom_eval₂]
    have hvx (j : J) : gaussianOmnificToSurcomplex (x j) =
        ofComplex (GaussianInt.toComplex (gaussianOmnificConstantCoeff (x j))) :=
      (congrArg gaussianOmnificToSurcomplex (h j)).trans (hv _)
    simpa only [hvx] using hx
  · rintro ⟨a, ha, hx⟩
    have he := congrArg ofComplex ha
    rw [MvPolynomial.hom_eval₂] at he
    simpa only [hx, hv] using he

end
end Surreal.Surcomplex
