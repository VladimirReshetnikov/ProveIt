import Surreal.Surcomplex.GaussianNormalizationEmbedding

/-!
# Coordinates and common monomial divisors in the Gaussian infinite ideal

The actual Gaussian instance of `osq:prop:common`(i), used to extend
`osq:thm:universal` from real to Gaussian omnific integers. Both coordinates
are cleared with the same real monomial; the quotient retains zero constant.
-/

universe u v
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- The purely infinite ideal of the actual Gaussian omnific ring. -/
abbrev gaussianOmnificPurelyInfiniteIdeal : Ideal GaussianOmnificInteger.{u} :=
  RingHom.ker gaussianOmnificConstantCoeff

/-- The ordinary imaginary unit as a Gaussian omnific integer. -/
def gaussianOmnificI : GaussianOmnificInteger.{u} := gaussianOmnificConstants ⟨0, 1⟩

@[simp] theorem gaussianOmnificI_value :
    gaussianOmnificToSurcomplex gaussianOmnificI = (I : Surcomplex.{u}) := by
  change ofComplex (GaussianInt.toComplex ⟨0, 1⟩) = I
  have he : GaussianInt.toComplex ⟨0, 1⟩ = Complex.I := by
    apply Complex.ext <;> simp
  rw [he, ofComplex_I]

/-- The two actual omnific coordinates reconstruct the original Gaussian element. -/
theorem gaussianOmnific_coordinate_decomposition (x : GaussianOmnificInteger.{u}) :
    x = omnificToGaussian (gaussianOmnificRe x) +
      omnificToGaussian (gaussianOmnificIm x) * gaussianOmnificI := by
  apply gaussianOmnificToSurcomplex_injective
  rw [map_add, map_mul, gaussianOmnificToSurcomplex_of_omnific,
    gaussianOmnificToSurcomplex_of_omnific, gaussianOmnificI_value,
    gaussianOmnificRe_value, gaussianOmnificIm_value, re_add_im_mul_I]

/-- Purely infinite Gaussian elements have purely infinite real and imaginary coordinates. -/
theorem gaussianOmnific_purelyInfinite_iff_coordinates (x : GaussianOmnificInteger.{u}) :
    x ∈ gaussianOmnificPurelyInfiniteIdeal ↔
      gaussianOmnificRe x ∈ SignSequence.omnificPurelyInfiniteIdeal ∧
      gaussianOmnificIm x ∈ SignSequence.omnificPurelyInfiniteIdeal := by
  have hr (z : SignSequence.OmnificInteger.{u}) :
      SignSequence.IsPurelyInfinite (SignSequence.omnificToSurreal z) ↔
        z ∈ SignSequence.omnificPurelyInfiniteIdeal :=
    (SignSequence.omnific_inf_iff z).symm.trans
      (SignSequence.omnific_purelyInfinite_iff_quadratic z).symm
  rw [← isPurelyInfinite_gaussianOmnific_iff, isPurelyInfinite_iff_re_im, ← hr, ← hr,
    gaussianOmnificRe_value, gaussianOmnificIm_value]

/-- Real inclusion takes the real purely infinite ideal into the Gaussian one. -/
theorem omnificToGaussian_mem_purelyInfinite (x : SignSequence.OmnificInteger.{u})
    (hx : x ∈ SignSequence.omnificPurelyInfiniteIdeal) :
    omnificToGaussian x ∈ gaussianOmnificPurelyInfiniteIdeal := by
  apply (isPurelyInfinite_gaussianOmnific_iff _).mp
  rw [gaussianOmnificToSurcomplex_of_omnific, isPurelyInfinite_iff_re_im, ofReal_re, ofReal_im]
  refine ⟨(SignSequence.omnific_inf_iff x).mp
    ((SignSequence.omnific_purelyInfinite_iff_quadratic x).mp hx), ?_⟩
  intro a _
  simp only [SignSequence.rawNormalForm_zero, _root_.HahnSeries.coeff_zero]

/-- A common real monomial divides any small family in the Gaussian infinite ideal. -/
theorem gaussianOmnific_common_monomial_divisor {ι : Type v} [Small.{u} ι]
    (s : ι → GaussianOmnificInteger.{u}) (hs : ∀ i, s i ∈ gaussianOmnificPurelyInfiniteIdeal) :
    ∃ (a : SignSequence.{u}) (ha : 0 < a), ∀ i,
      ∃ q ∈ gaussianOmnificPurelyInfiniteIdeal,
        s i = omnificToGaussian (SignSequence.omnificMonomial a ha) * q := by
  let coords : ι × Bool → SignSequence.OmnificInteger.{u} := fun p =>
    if p.2 then gaussianOmnificIm (s p.1) else gaussianOmnificRe (s p.1)
  have hc (p : ι × Bool) : coords p ∈ SignSequence.omnificPurelyInfiniteIdeal := by
    have hp := (gaussianOmnific_purelyInfinite_iff_coordinates (s p.1)).mp (hs p.1)
    dsimp [coords]
    split_ifs
    · exact hp.2
    · exact hp.1
  obtain ⟨a, ha, hd⟩ := SignSequence.omnific_common_monomial_divisor coords hc
  refine ⟨a, ha, fun i => ?_⟩
  obtain ⟨qr, hqr, her⟩ := hd (i, false)
  obtain ⟨qi, hqi, hei⟩ := hd (i, true)
  change gaussianOmnificRe (s i) = SignSequence.omnificMonomial a ha * qr at her
  change gaussianOmnificIm (s i) = SignSequence.omnificMonomial a ha * qi at hei
  refine ⟨omnificToGaussian qr + omnificToGaussian qi * gaussianOmnificI,
    gaussianOmnificPurelyInfiniteIdeal.add_mem (omnificToGaussian_mem_purelyInfinite qr hqr)
      (gaussianOmnificPurelyInfiniteIdeal.mul_mem_right _
        (omnificToGaussian_mem_purelyInfinite qi hqi)), ?_⟩
  conv_lhs => rw [gaussianOmnific_coordinate_decomposition (s i), her, hei, map_mul, map_mul]
  ring

/-- Gaussian constant extraction has its usual additive decomposition inside the ring. -/
theorem gaussianOmnific_constant_remainder (x : GaussianOmnificInteger.{u}) :
    x - gaussianOmnificConstants (gaussianOmnificConstantCoeff x) ∈ gaussianOmnificPurelyInfiniteIdeal := by
  change gaussianOmnificConstantCoeff (_ - _) = 0
  rw [map_sub, gaussianOmnificConstantCoeff_constants, sub_self]

end
end Surreal.Surcomplex
