import Surreal.Algebra.GaussianPrimeQuotients
import Surreal.Surcomplex.GaussianSmallQuotients
import Mathlib.RingTheory.Localization.FractionRing

/-!
# Gaussian omnific prime ideals with small quotient

The Gaussian instance of `osq:cor:smallprimes`. The purely infinite ideal
is prime but not maximal; all remaining small prime quotients are the
finite fields at ordinary Gaussian prime moduli.
-/

universe u v
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- The purely infinite Gaussian ideal has an ordinary Gaussian integer domain as quotient. -/
theorem gaussianOmnificPurelyInfiniteIdeal_isPrime :
    gaussianOmnificPurelyInfiniteIdeal.{u}.IsPrime :=
  Ideal.comap_isPrime gaussianOmnificConstantCoeff.{u} ⊥

/-- This characteristic-zero quotient is not a field, so its kernel is not maximal. -/
theorem gaussianOmnificPurelyInfiniteIdeal_not_isMaximal :
    ¬ gaussianOmnificPurelyInfiniteIdeal.{u}.IsMaximal := by
  intro h
  have hf := (Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mp h
  let e := gaussianOmnificConstantCoeff.{u}.quotientKerEquivOfSurjective
    gaussianOmnificConstantCoeff_surjective
  exact GaussianQuotientCardinality.not_isField (e.symm.toMulEquiv.isField hf)

/-- Nonzero Gaussian constant moduli generate prime omnific ideals exactly when Gaussian prime. -/
theorem gaussianOmnific_constant_span_isPrime_iff (d : GaussianInt) (hd : d ≠ 0) :
    (Ideal.span {gaussianOmnificConstants.{u} d}).IsPrime ↔ Prime d := by
  constructor
  · intro h
    letI := h
    have he : (Ideal.span {gaussianOmnificConstants.{u} d}).comap gaussianOmnificConstants.{u} =
        Ideal.span {d} := by
      ext x
      rw [Ideal.mem_comap, Ideal.mem_span_singleton, gaussianOmnific_constant_dvd_iff d hd,
        gaussianOmnificConstantCoeff_constants, Ideal.mem_span_singleton]
    have hp := Ideal.comap_isPrime gaussianOmnificConstants.{u}
      (Ideal.span {gaussianOmnificConstants.{u} d})
    rw [he] at hp
    exact (Ideal.span_singleton_prime hd).mp hp
  · intro hp
    letI : (Ideal.span {d}).IsPrime := (Ideal.span_singleton_prime hd).mpr hp
    rw [← gaussianOmnific_comap_span d hd]
    exact Ideal.comap_isPrime gaussianOmnificConstantCoeff.{u} (Ideal.span {d})

/-- Ordinary Gaussian primes generate maximal actual Gaussian omnific ideals. -/
theorem gaussianOmnific_prime_span_isMaximal (d : GaussianInt) (hd : Prime d) :
    (Ideal.span {gaussianOmnificConstants.{u} d}).IsMaximal := by
  letI := GaussianQuotientCardinality.prime_span_isMaximal d hd
  rw [← gaussianOmnific_comap_span d hd.ne_zero]
  exact Ideal.comap_isMaximal_of_surjective gaussianOmnificConstantCoeff.{u}
    gaussianOmnificConstantCoeff_surjective

/-- The complete prime classification among ideals with birthday-universe-small quotient. -/
theorem gaussianOmnific_small_ideal_isPrime_iff (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    I.IsPrime ↔ I = gaussianOmnificPurelyInfiniteIdeal.{u} ∨
      ∃ d : GaussianInt, Prime d ∧ I = Ideal.span {gaussianOmnificConstants.{u} d} := by
  constructor
  · intro h
    rcases gaussianOmnific_small_quotient_kernel_cases I with hI | ⟨d, hd, hI⟩
    · exact Or.inl hI
    · exact Or.inr ⟨d, (gaussianOmnific_constant_span_isPrime_iff d hd).mp (hI ▸ h), hI⟩
  · rintro (rfl | ⟨d, hd, rfl⟩)
    · exact gaussianOmnificPurelyInfiniteIdeal_isPrime
    · exact (gaussianOmnific_constant_span_isPrime_iff d hd.ne_zero).mpr hd

/-- All small maximal quotients have Gaussian prime modulus; Pi is excluded. -/
theorem gaussianOmnific_small_ideal_isMaximal_iff (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    I.IsMaximal ↔ ∃ d : GaussianInt, Prime d ∧ I = Ideal.span {gaussianOmnificConstants.{u} d} := by
  constructor
  · intro h
    rcases (gaussianOmnific_small_ideal_isPrime_iff I).mp h.isPrime with hI | hI
    · exact False.elim (gaussianOmnificPurelyInfiniteIdeal_not_isMaximal (hI ▸ h))
    · exact hI
  · rintro ⟨d, hd, rfl⟩
    exact gaussianOmnific_prime_span_isMaximal d hd

/-- Precisely the Gaussian prime moduli give small field quotients. -/
theorem gaussianOmnific_small_quotient_isField_iff (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    IsField (GaussianOmnificInteger.{u} ⧸ I) ↔
      ∃ d : GaussianInt, Prime d ∧ I = Ideal.span {gaussianOmnificConstants.{u} d} := by
  rw [← Ideal.Quotient.maximal_ideal_iff_isField_quotient,
    gaussianOmnific_small_ideal_isMaximal_iff]

/-- Every small Gaussian omnific field quotient is the ordinary finite Gaussian residue field. -/
theorem gaussianOmnific_small_field_quotient (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] (hf : IsField (GaussianOmnificInteger.{u} ⧸ I)) :
    ∃ d : GaussianInt, Prime d ∧ I = Ideal.span {gaussianOmnificConstants.{u} d} ∧
      Finite (GaussianOmnificInteger.{u} ⧸ I) ∧
      Nat.card (GaussianOmnificInteger.{u} ⧸ I) = d.norm.natAbs ∧
      Nonempty ((GaussianOmnificInteger.{u} ⧸ I) ≃+* GaussianInt ⧸ Ideal.span {d}) := by
  obtain ⟨d, hd, rfl⟩ := (gaussianOmnific_small_ideal_isMaximal_iff I).mp
    ((Ideal.Quotient.maximal_ideal_iff_isField_quotient _).mpr hf)
  exact ⟨d, hd, rfl, gaussianOmnific_quotient_finite d hd.ne_zero,
    gaussianOmnific_quotient_card d hd.ne_zero, ⟨gaussianOmnificQuotientConstantEquiv d hd.ne_zero⟩⟩

/-- In characteristic zero, every small Gaussian omnific image has exactly the infinite kernel. -/
theorem gaussianOmnific_small_charZero_ker {K : Type v}
    [Ring K] [CharZero K] [Small.{u} K] (φ : GaussianOmnificInteger.{u} →+* K) :
    RingHom.ker φ = gaussianOmnificPurelyInfiniteIdeal.{u} := by
  have hi := GaussianQuotientCardinality.ringHom_injective_charZero
    (φ.comp gaussianOmnificConstants.{u})
  ext x
  change φ x = 0 ↔ gaussianOmnificConstantCoeff.{u} x = 0
  have he := gaussianOmnific_small_hom_eq_constant φ.toNonUnitalRingHom x
  change φ x = φ (gaussianOmnificConstants.{u} (gaussianOmnificConstantCoeff.{u} x)) at he
  rw [he]
  exact map_eq_zero_iff (φ.comp gaussianOmnificConstants.{u}) hi

/-- A small characteristic-zero image is the ordinary Gaussian integer ring. -/
def gaussianOmnificSmallCharZeroRangeEquiv {K : Type v}
    [Ring K] [CharZero K] [Small.{u} K] (φ : GaussianOmnificInteger.{u} →+* K) :
    φ.range ≃+* GaussianInt :=
  (RingHom.quotientKerEquivRange φ).symm.trans
    ((Ideal.quotEquivOfEq (gaussianOmnific_small_charZero_ker φ)).trans
      (gaussianOmnificConstantCoeff.{u}.quotientKerEquivOfSurjective
        gaussianOmnificConstantCoeff_surjective))

/-- In particular that characteristic-zero image is not a field. -/
theorem gaussianOmnific_small_charZero_range_not_isField {K : Type v}
    [Ring K] [CharZero K] [Small.{u} K] (φ : GaussianOmnificInteger.{u} →+* K) :
    ¬ IsField φ.range := by
  intro h
  exact GaussianQuotientCardinality.not_isField
    ((gaussianOmnificSmallCharZeroRangeEquiv φ).symm.toMulEquiv.isField h)

/-- A map to a small field has one of the classified small prime kernels. -/
theorem gaussianOmnific_small_field_ker {K : Type v} [Field K] [Small.{u} K]
    (φ : GaussianOmnificInteger.{u} →+* K) :
    RingHom.ker φ = gaussianOmnificPurelyInfiniteIdeal.{u} ∨
      ∃ d : GaussianInt, Prime d ∧ RingHom.ker φ = Ideal.span {gaussianOmnificConstants.{u} d} := by
  letI : Small.{u} (GaussianOmnificInteger.{u} ⧸ RingHom.ker φ) :=
    small_of_injective (RingHom.quotientKerEquivRange φ).injective
  exact (gaussianOmnific_small_ideal_isPrime_iff (RingHom.ker φ)).mp (Ideal.comap_isPrime φ ⊥)

/-- Nonzero characteristic excludes the infinite-ideal case, leaving a Gaussian prime modulus. -/
theorem gaussianOmnific_small_charP_field_ker {K : Type v} [Field K] [Small.{u} K]
    (p : ℕ) (hp : p ≠ 0) [CharP K p] (φ : GaussianOmnificInteger.{u} →+* K) :
    ∃ d : GaussianInt, Prime d ∧ RingHom.ker φ = Ideal.span {gaussianOmnificConstants.{u} d} := by
  rcases gaussianOmnific_small_field_ker φ with h | h
  · have hz : gaussianOmnificConstants.{u} (p : GaussianInt) ∈ RingHom.ker φ := by
      rw [RingHom.mem_ker, map_natCast, map_natCast, CharP.cast_eq_zero K p]
    rw [h] at hz
    change gaussianOmnificConstantCoeff.{u} (gaussianOmnificConstants.{u} (p : GaussianInt)) = 0 at hz
    rw [gaussianOmnificConstantCoeff_constants, Nat.cast_eq_zero] at hz
    exact False.elim (hp hz)
  · exact h

/-- A positive-characteristic small field image is a finite ordinary Gaussian residue field. -/
theorem gaussianOmnific_small_charP_field_image {K : Type v} [Field K] [Small.{u} K]
    (p : ℕ) (hp : p ≠ 0) [CharP K p] (φ : GaussianOmnificInteger.{u} →+* K) :
    ∃ d : GaussianInt, Prime d ∧
      Nonempty (φ.range ≃+* GaussianInt ⧸ Ideal.span {d}) ∧
      IsField φ.range ∧ Finite φ.range ∧ Nat.card φ.range = d.norm.natAbs := by
  obtain ⟨d, hd, he⟩ := gaussianOmnific_small_charP_field_ker p hp φ
  let e := (RingHom.quotientKerEquivRange φ).symm.trans
    ((Ideal.quotEquivOfEq he).trans (gaussianOmnificQuotientConstantEquiv d hd.ne_zero))
  have h := GaussianQuotientCardinality.prime_quotient d hd
  letI := h.2.1
  exact ⟨d, hd, ⟨e⟩, e.toMulEquiv.isField h.1, Finite.of_injective e e.injective,
    (Nat.card_congr e.toEquiv).trans h.2.2⟩

/-- Taking fractions of the infinite-ideal quotient yields the ordinary Gaussian fraction field. -/
def gaussianOmnificPurelyInfiniteFractionEquiv :
    FractionRing (GaussianOmnificInteger.{u} ⧸ gaussianOmnificPurelyInfiniteIdeal.{u}) ≃+*
      FractionRing GaussianInt :=
  IsFractionRing.ringEquivOfRingEquiv
    (gaussianOmnificConstantCoeff.{u}.quotientKerEquivOfSurjective
      gaussianOmnificConstantCoeff_surjective)

/-- Taking fractions of a Gaussian prime quotient leaves its finite residue field unchanged. -/
def gaussianOmnificPrimeFractionEquiv (d : GaussianInt) (hd : Prime d) :
    FractionRing (GaussianOmnificInteger.{u} ⧸ Ideal.span {gaussianOmnificConstants.{u} d}) ≃+*
      GaussianInt ⧸ Ideal.span {d} := by
  letI := (GaussianQuotientCardinality.prime_quotient d hd).1.toField
  exact IsFractionRing.ringEquivOfRingEquiv (gaussianOmnificQuotientConstantEquiv d hd.ne_zero)

end
end Surreal.Surcomplex
