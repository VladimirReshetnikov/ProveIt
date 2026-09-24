import Surreal.Surcomplex.DecomposableFibers
import Mathlib.NumberTheory.Zsqrtd.GaussianInt

/-!
# Actual Gaussian omnific integers

The ring `Og = Z[i] + Pi_C` preceding `odg:dec:thm:gaussianfibers`.
It is the pullback of Mathlib's Gaussian integers along the actual complex
constant-term homomorphism. Equivalently, both real coordinates are omnific.
-/

universe u
namespace Surreal.Surcomplex

open Foundations

noncomputable section

attribute [local instance] nonnegativeSupportComplexAlgebra

/-- The actual complex support subring with Gaussian integer constant coefficient. -/
def gaussianOmnificSubring : Subring nonnegativeSupportSubring.{u} :=
  CoefficientPullback.subring constantCoeff GaussianInt.toComplex

/-- Gaussian omnific integers, retaining their actual surcomplex values. -/
abbrev GaussianOmnificInteger : Type (u + 1) := gaussianOmnificSubring.{u}

/-- The embedding in the actual surcomplex field. -/
def gaussianOmnificToSurcomplex : GaussianOmnificInteger.{u} →+* Surcomplex.{u} :=
  nonnegativeSupportSubring.subtype.comp gaussianOmnificSubring.subtype

/-- Gaussian constant extraction on the actual Gaussian omnific ring. -/
def gaussianOmnificConstantCoeff : GaussianOmnificInteger.{u} →+* GaussianInt :=
  CoefficientPullback.retraction constantCoeff GaussianInt.toComplex GaussianInt.toComplex_injective

/-- Ordinary Gaussian integers embed as constant Gaussian omnific integers. -/
def gaussianOmnificConstants : GaussianInt →+* GaussianOmnificInteger.{u} :=
  CoefficientPullback.sectionMap constantCoeff GaussianInt.toComplex complexConstants
    constantCoeff_complexConstants

@[simp] theorem gaussianOmnificConstantCoeff_constants (a : GaussianInt) :
    gaussianOmnificConstantCoeff (gaussianOmnificConstants.{u} a) = a :=
  CoefficientPullback.retraction_sectionMap _ _ _ _ _ a

@[simp] theorem gaussianOmnificConstantCoeff_toComplex (x : GaussianOmnificInteger.{u}) :
    GaussianInt.toComplex (gaussianOmnificConstantCoeff x) = constantCoeff x.val :=
  CoefficientPullback.embedding_retraction _ _ _ x

@[simp] theorem gaussianOmnificConstants_val (a : GaussianInt) :
    (gaussianOmnificConstants.{u} a).val = complexConstants (GaussianInt.toComplex a) := rfl

/-- The pullback condition is exactly the condition that both coordinates are omnific. -/
theorem mem_gaussianOmnificSubring_iff (z : nonnegativeSupportSubring.{u}) :
    z ∈ gaussianOmnificSubring ↔
      nonnegativeRe z ∈ SignSequence.omnificSubring ∧
      nonnegativeIm z ∈ SignSequence.omnificSubring := by
  change (∃ a : GaussianInt, GaussianInt.toComplex a = constantCoeff z) ↔
    (∃ a : ℤ, (a : ℝ) = SignSequence.constantCoeff (nonnegativeRe z)) ∧
    (∃ b : ℤ, (b : ℝ) = SignSequence.constantCoeff (nonnegativeIm z))
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨⟨a.re, (GaussianInt.intCast_re a).trans (congrArg Complex.re ha)⟩,
      ⟨a.im, (GaussianInt.intCast_im a).trans (congrArg Complex.im ha)⟩⟩
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    refine ⟨⟨a, b⟩, ?_⟩
    apply Complex.ext
    · rw [GaussianInt.re_toComplex]
      exact ha
    · rw [GaussianInt.im_toComplex]
      exact hb

/-- The complex purely infinite ideal, regarded as a vector space over the ordinary complexes. -/
def complexPurelyInfiniteSubmodule : Submodule ℂ nonnegativeSupportSubring.{u} :=
  purelyInfiniteIdeal.restrictScalars ℂ

/-- Purely infinite complex elements have zero constant coefficient. -/
theorem complexPurelyInfinite_constant_zero (v : complexPurelyInfiniteSubmodule.{u}) :
    constantCoeff v.val = 0 := v.property

/-- Every purely infinite complex element belongs to the Gaussian omnific ring. -/
def complexPurelyInfiniteToGaussian : complexPurelyInfiniteSubmodule.{u} →
    GaussianOmnificInteger.{u} := fun v =>
  ⟨v.val, ⟨0, by rw [map_zero, complexPurelyInfinite_constant_zero]⟩⟩

/-- Every Gaussian omnific integer splits into its ordinary Gaussian constant and infinite part. -/
theorem gaussianOmnific_constant_decomposition (x : GaussianOmnificInteger.{u}) :
    ∃ v : complexPurelyInfiniteSubmodule.{u},
      x.val = complexConstants (GaussianInt.toComplex (gaussianOmnificConstantCoeff x)) + v.val := by
  refine ⟨⟨x.val - complexConstants (constantCoeff x.val), ?_⟩, ?_⟩
  · change constantCoeff (x.val - complexConstants (constantCoeff x.val)) = 0
    rw [map_sub, constantCoeff_complexConstants, sub_self]
  · rw [gaussianOmnificConstantCoeff_toComplex]
    change x.val = complexConstants (constantCoeff x.val) +
      (x.val - complexConstants (constantCoeff x.val))
    abel

/-- The ordinary Gaussian part of a split is unique, so distinct ordinary fibers are disjoint. -/
theorem gaussianOmnific_split_constant_unique (a b : GaussianInt)
    (v w : complexPurelyInfiniteSubmodule.{u})
    (h : complexConstants (GaussianInt.toComplex a) + v.val =
      complexConstants (GaussianInt.toComplex b) + w.val) : a = b := by
  apply GaussianInt.toComplex_injective
  have hc := congrArg constantCoeff h
  simpa only [map_add, constantCoeff_complexConstants, complexPurelyInfinite_constant_zero,
    add_zero] using hc

end
end Surreal.Surcomplex
