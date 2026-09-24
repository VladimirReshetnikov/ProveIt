import Surreal.Surcomplex.GaussianPurelyInfiniteIdeal

/-!
# Common monomials in small families of kernels

The actual real and Gaussian instances of `osq:rep:cor:kernels`. Denominator
clearing first gives a common monomial multiple of any small family of nonzero
omnific integers. Consequently a specified nonzero witness in each kernel
forces a common nonzero monomial in all kernels. Only the index type must be
small; the target rings may live in an arbitrary universe. Empty families are
included.
-/

universe u v w
namespace Surreal.Foundations.SignSequence

/-- A small nonzero family divides one positive monomial, with purely infinite quotients. -/
theorem omnific_common_monomial_multiple {ι : Type v} [Small.{u} ι]
    (b : ι → OmnificInteger.{u}) (hb : ∀ i, b i ≠ 0) :
    ∃ (δ : SignSequence.{u}) (hδ : 0 < δ), ∀ i,
      ∃ q ∈ omnificPurelyInfiniteIdeal, omnificMonomial δ hδ = q * b i := by
  obtain ⟨δ, hδ, h⟩ := omnific_monomial_clearing (fun i => (omnificToSurreal (b i))⁻¹)
  refine ⟨δ, hδ, fun i => ?_⟩
  obtain ⟨q, hq, he⟩ := h i
  refine ⟨q, hq, omnificToSurreal_injective ?_⟩
  have hn := (map_ne_zero_iff omnificToSurreal omnificToSurreal_injective).mpr (hb i)
  rw [omnificToSurreal_monomial, map_mul, he, mul_assoc, inv_mul_cancel₀ hn, mul_one]

/-- Specified nonzero kernel witnesses yield one positive monomial in every kernel. -/
theorem omnific_common_kernel_monomial {ι : Type v} [Small.{u} ι]
    {B : ι → Type w} [∀ i, Ring (B i)] (φ : ∀ i, OmnificInteger.{u} →+* B i)
    (b : ι → OmnificInteger.{u}) (hb : ∀ i, b i ≠ 0) (hk : ∀ i, φ i (b i) = 0) :
    ∃ (δ : SignSequence.{u}) (hδ : 0 < δ),
      omnificMonomial δ hδ ≠ 0 ∧ ∀ i, φ i (omnificMonomial δ hδ) = 0 := by
  obtain ⟨δ, hδ, h⟩ := omnific_common_monomial_multiple b hb
  refine ⟨δ, hδ, omnificMonomial_ne_zero δ hδ, fun i => ?_⟩
  obtain ⟨q, _, he⟩ := h i
  rw [he, map_mul, hk, mul_zero]

/-- A small family with specified nonzero kernel witnesses is not jointly injective. -/
theorem omnific_not_jointly_injective {ι : Type v} [Small.{u} ι]
    {B : ι → Type w} [∀ i, Ring (B i)] (φ : ∀ i, OmnificInteger.{u} →+* B i)
    (b : ι → OmnificInteger.{u}) (hb : ∀ i, b i ≠ 0) (hk : ∀ i, φ i (b i) = 0) :
    ¬ Function.Injective (fun x i => φ i x) := by
  obtain ⟨δ, hδ, hn, h⟩ := omnific_common_kernel_monomial φ b hb hk
  intro hi
  exact hn (hi (funext fun i => (h i).trans (map_zero (φ i)).symm))

end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations

/-- A small nonzero Gaussian family divides one positive real monomial. -/
theorem gaussianOmnific_common_monomial_multiple {ι : Type v} [Small.{u} ι]
    (b : ι → GaussianOmnificInteger.{u}) (hb : ∀ i, b i ≠ 0) :
    ∃ (δ : SignSequence.{u}) (hδ : 0 < δ), ∀ i,
      ∃ q ∈ gaussianOmnificPurelyInfiniteIdeal,
        omnificToGaussian (SignSequence.omnificMonomial δ hδ) = q * b i := by
  obtain ⟨δ, hδ, h⟩ := gaussianOmnific_monomial_clearing
    (fun i => (gaussianOmnificToSurcomplex (b i))⁻¹)
  refine ⟨δ, hδ, fun i => ?_⟩
  obtain ⟨q, hq, he⟩ := h i
  refine ⟨q, hq, gaussianOmnificToSurcomplex_injective ?_⟩
  have hn := (map_ne_zero_iff gaussianOmnificToSurcomplex.{u}
    gaussianOmnificToSurcomplex_injective).mpr (hb i)
  rw [gaussianOmnificToSurcomplex_of_omnific, SignSequence.omnificToSurreal_monomial,
    map_mul, he, mul_assoc, inv_mul_cancel₀ hn, mul_one]

/-- Gaussian kernel witnesses give a common nonzero positive real monomial. -/
theorem gaussianOmnific_common_kernel_monomial {ι : Type v} [Small.{u} ι]
    {B : ι → Type w} [∀ i, Ring (B i)] (φ : ∀ i, GaussianOmnificInteger.{u} →+* B i)
    (b : ι → GaussianOmnificInteger.{u}) (hb : ∀ i, b i ≠ 0) (hk : ∀ i, φ i (b i) = 0) :
    ∃ (δ : SignSequence.{u}) (hδ : 0 < δ),
      omnificToGaussian (SignSequence.omnificMonomial δ hδ) ≠ 0 ∧
        ∀ i, φ i (omnificToGaussian (SignSequence.omnificMonomial δ hδ)) = 0 := by
  obtain ⟨δ, hδ, h⟩ := gaussianOmnific_common_monomial_multiple b hb
  refine ⟨δ, hδ, ?_, fun i => ?_⟩
  · intro hz
    have he := congrArg gaussianOmnificToSurcomplex hz
    rw [gaussianOmnificToSurcomplex_of_omnific, SignSequence.omnificToSurreal_monomial,
      map_zero] at he
    exact ((map_ne_zero_iff ofReal ofReal_injective).mpr
      (SignSequence.omegaPower_ne_zero δ)) he
  · obtain ⟨q, _, he⟩ := h i
    rw [he, map_mul, hk, mul_zero]

/-- Such a small Gaussian family cannot jointly distinguish all elements. -/
theorem gaussianOmnific_not_jointly_injective {ι : Type v} [Small.{u} ι]
    {B : ι → Type w} [∀ i, Ring (B i)] (φ : ∀ i, GaussianOmnificInteger.{u} →+* B i)
    (b : ι → GaussianOmnificInteger.{u}) (hb : ∀ i, b i ≠ 0) (hk : ∀ i, φ i (b i) = 0) :
    ¬ Function.Injective (fun x i => φ i x) := by
  obtain ⟨δ, hδ, hn, h⟩ := gaussianOmnific_common_kernel_monomial φ b hb hk
  intro hi
  exact hn (hi (funext fun i => (h i).trans (map_zero (φ i)).symm))

end Surreal.Surcomplex
