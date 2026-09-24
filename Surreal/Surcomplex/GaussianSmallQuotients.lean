import Surreal.Algebra.GaussianQuotientCardinality
import Surreal.Algebra.QuotientReflection
import Surreal.Algebra.CoefficientPullbackDivisibility
import Surreal.Surcomplex.GaussianSmallTargets
import Mathlib.RingTheory.PrincipalIdealDomain

/-!
# Small Gaussian omnific quotients

The actual Gaussian instances of `osq:thm:reflection` and the ideal
classification in `osq:thm:quotients`. Every small quotient is exactly an
ordinary Gaussian quotient, and nonzero ordinary Gaussian moduli generate
its principal kernels. Every nonzero ordinary Gaussian modulus has a finite
quotient of cardinality equal to its squared complex modulus.
-/

universe u v
namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Every ordinary Gaussian integer occurs as a constant coefficient. -/
theorem gaussianOmnificConstantCoeff_surjective :
    Function.Surjective (gaussianOmnificConstantCoeff.{u}) :=
  fun d => ⟨gaussianOmnificConstants.{u} d, gaussianOmnificConstantCoeff_constants d⟩

/-- Pulling back the Gaussian image ideal adds precisely the infinite ideal. -/
theorem gaussianOmnific_comap_map_constant (I : Ideal GaussianOmnificInteger.{u}) :
    (I.map gaussianOmnificConstantCoeff.{u}).comap gaussianOmnificConstantCoeff.{u} =
      gaussianOmnificPurelyInfiniteIdeal.{u} ⊔ I :=
  QuotientReflection.comap_map gaussianOmnificConstantCoeff.{u} gaussianOmnificConstantCoeff_surjective I

/-- Canonical reflection of any actual Gaussian omnific quotient into its ordinary quotient. -/
def gaussianOmnificQuotientReflection (I : Ideal GaussianOmnificInteger.{u}) :
    (GaussianOmnificInteger.{u} ⧸ I) →+* GaussianInt ⧸ I.map gaussianOmnificConstantCoeff.{u} :=
  QuotientReflection.reflection gaussianOmnificConstantCoeff.{u} I

/-- The reflection has exactly the predicted image of the infinite ideal as kernel. -/
theorem gaussianOmnificQuotientReflection_ker (I : Ideal GaussianOmnificInteger.{u}) :
    RingHom.ker (gaussianOmnificQuotientReflection I) =
      (gaussianOmnificPurelyInfiniteIdeal.{u} ⊔ I).map (Ideal.Quotient.mk I) :=
  QuotientReflection.reflection_ker gaussianOmnificConstantCoeff.{u}
    gaussianOmnificConstantCoeff_surjective I

/-- The ordinary reflection has exactly the same maps into every small target ring. -/
def gaussianOmnificQuotientSmallHomEquiv (I : Ideal GaussianOmnificInteger.{u})
    (S : Type v) [Ring S] [Small.{u} S] :
    ((GaussianOmnificInteger.{u} ⧸ I) →+* S) ≃
      ((GaussianInt ⧸ I.map gaussianOmnificConstantCoeff.{u}) →+* S) :=
  QuotientReflection.homEquiv gaussianOmnificConstantCoeff.{u} gaussianOmnificConstants.{u}
    gaussianOmnificConstantCoeff_constants
    (fun φ x => gaussianOmnific_small_hom_eq_constant φ.toNonUnitalRingHom x) I

/-- A Gaussian omnific quotient is small exactly when its ideal contains all infinite parts. -/
theorem gaussianOmnific_small_quotient_iff (I : Ideal GaussianOmnificInteger.{u}) :
    Small.{u} (GaussianOmnificInteger.{u} ⧸ I) ↔ gaussianOmnificPurelyInfiniteIdeal.{u} ≤ I := by
  constructor
  · intro h
    letI := h
    intro x hx
    exact Ideal.Quotient.eq_zero_iff_mem.mp
      (gaussianOmnific_small_hom_purelyInfinite (Ideal.Quotient.mk I).toNonUnitalRingHom x hx)
  · intro hI
    exact QuotientReflection.small_quotient_of_ker_le gaussianOmnificConstantCoeff.{u}
      gaussianOmnificConstantCoeff_surjective I hI

/-- The ordinary Gaussian ideal associated to a small quotient is unique. -/
theorem gaussianOmnific_small_quotient_ideal_unique (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    ∃! J : Ideal GaussianInt, I = J.comap gaussianOmnificConstantCoeff.{u} :=
  QuotientReflection.ideal_correspondence gaussianOmnificConstantCoeff.{u}
    gaussianOmnificConstantCoeff_surjective I ((gaussianOmnific_small_quotient_iff I).mp inferInstance)

/-- A small Gaussian omnific quotient is its native ordinary Gaussian quotient. -/
def gaussianOmnificSmallQuotientEquiv (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    (GaussianOmnificInteger.{u} ⧸ I) ≃+* GaussianInt ⧸ I.map gaussianOmnificConstantCoeff.{u} :=
  QuotientReflection.quotientEquiv gaussianOmnificConstantCoeff.{u}
    gaussianOmnificConstantCoeff_surjective I ((gaussianOmnific_small_quotient_iff I).mp inferInstance)

/-- Divisibility by a nonzero Gaussian constant is equivalent to ordinary constant divisibility. -/
theorem gaussianOmnific_constant_dvd_iff (d : GaussianInt) (hd : d ≠ 0)
    (x : GaussianOmnificInteger.{u}) :
    gaussianOmnificConstants.{u} d ∣ x ↔ d ∣ gaussianOmnificConstantCoeff.{u} x :=
  CoefficientPullback.sectionMap_dvd_iff constantCoeff GaussianInt.toComplex
    GaussianInt.toComplex_injective complexConstants constantCoeff_complexConstants d
    ((map_ne_zero_iff GaussianInt.toComplex GaussianInt.toComplex_injective).mpr hd) x

/-- The inverse image of a nonzero principal Gaussian ideal is the same principal omnific ideal. -/
theorem gaussianOmnific_comap_span (d : GaussianInt) (hd : d ≠ 0) :
    (Ideal.span {d}).comap gaussianOmnificConstantCoeff.{u} = Ideal.span {gaussianOmnificConstants.{u} d} := by
  ext x
  rw [Ideal.mem_comap, Ideal.mem_span_singleton, Ideal.mem_span_singleton,
    gaussianOmnific_constant_dvd_iff d hd]

/-- The quotient by a nonzero Gaussian constant is the ordinary Gaussian residue ring. -/
def gaussianOmnificQuotientConstantEquiv (d : GaussianInt) (hd : d ≠ 0) :
    (GaussianOmnificInteger.{u} ⧸ Ideal.span {gaussianOmnificConstants.{u} d}) ≃+*
      GaussianInt ⧸ Ideal.span {d} :=
  (Ideal.quotEquivOfEq (gaussianOmnific_comap_span d hd).symm).trans
    (QuotientReflection.quotientComapEquiv gaussianOmnificConstantCoeff.{u}
      gaussianOmnificConstantCoeff_surjective (Ideal.span {d}))

/-- Two Gaussian constant moduli define the same small kernel exactly when they are associates. -/
theorem gaussianOmnific_constant_kernels_eq_iff (d e : GaussianInt) :
    (Ideal.span {d}).comap gaussianOmnificConstantCoeff.{u} =
      (Ideal.span {e}).comap gaussianOmnificConstantCoeff.{u} ↔ Associated d e := by
  rw [(Ideal.comap_injective_of_surjective gaussianOmnificConstantCoeff.{u}
    gaussianOmnificConstantCoeff_surjective).eq_iff, Ideal.span_singleton_eq_span_singleton]

/-- Every small kernel has one Gaussian generator at the constant level. -/
theorem gaussianOmnific_small_quotient_generator (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    ∃ d : GaussianInt, I = (Ideal.span {d}).comap gaussianOmnificConstantCoeff.{u} := by
  obtain ⟨J, hJ, _⟩ := gaussianOmnific_small_quotient_ideal_unique I
  exact ⟨Submodule.IsPrincipal.generator J, by rw [Ideal.span_singleton_generator]; exact hJ⟩

/-- The small Gaussian kernels are the infinite ideal or nonzero ordinary Gaussian principal ideals. -/
theorem gaussianOmnific_small_quotient_kernel_cases (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    I = gaussianOmnificPurelyInfiniteIdeal.{u} ∨
      ∃ d : GaussianInt, d ≠ 0 ∧ I = Ideal.span {gaussianOmnificConstants.{u} d} := by
  obtain ⟨d, hd⟩ := gaussianOmnific_small_quotient_generator I
  by_cases hz : d = 0
  · left
    subst d
    change I = Ideal.comap gaussianOmnificConstantCoeff.{u} ⊥
    simpa only [Ideal.span_singleton_eq_bot.mpr rfl] using hd
  · exact Or.inr ⟨d, hz, hd.trans (gaussianOmnific_comap_span d hz)⟩

/-- The actual Gaussian omnific residue cardinality is the ordinary Gaussian norm. -/
theorem gaussianOmnific_quotient_card (d : GaussianInt) (hd : d ≠ 0) :
    Nat.card (GaussianOmnificInteger.{u} ⧸ Ideal.span {gaussianOmnificConstants.{u} d}) =
      d.norm.natAbs :=
  (Nat.card_congr (gaussianOmnificQuotientConstantEquiv d hd).toEquiv).trans
    (GaussianQuotientCardinality.card_quotient d)

/-- Every nonzero ordinary Gaussian modulus yields a finite actual omnific quotient. -/
theorem gaussianOmnific_quotient_finite (d : GaussianInt) (hd : d ≠ 0) :
    Finite (GaussianOmnificInteger.{u} ⧸ Ideal.span {gaussianOmnificConstants.{u} d}) := by
  apply Nat.finite_of_card_ne_zero
  rw [gaussianOmnific_quotient_card d hd]
  exact Int.natAbs_ne_zero.mpr (GaussianInt.norm_eq_zero.not.mpr hd)

/-- In complex notation the exact residue cardinality is the squared modulus of the Gaussian divisor. -/
theorem gaussianOmnific_quotient_card_normSq (d : GaussianInt) (hd : d ≠ 0) :
    (Nat.card (GaussianOmnificInteger.{u} ⧸ Ideal.span {gaussianOmnificConstants.{u} d}) : ℝ) =
      Complex.normSq (GaussianInt.toComplex d) := by
  rw [gaussianOmnific_quotient_card d hd, GaussianInt.natCast_natAbs_norm,
    GaussianInt.intCast_real_norm]

/-- The full Gaussian small-quotient classification, with exact finite sizes. -/
theorem gaussianOmnific_small_quotient_classification (I : Ideal GaussianOmnificInteger.{u})
    [Small.{u} (GaussianOmnificInteger.{u} ⧸ I)] :
    (I = gaussianOmnificPurelyInfiniteIdeal.{u} ∧
      Nonempty ((GaussianOmnificInteger.{u} ⧸ I) ≃+* GaussianInt)) ∨
    ∃ d : GaussianInt, d ≠ 0 ∧ I = Ideal.span {gaussianOmnificConstants.{u} d} ∧
      Finite (GaussianOmnificInteger.{u} ⧸ I) ∧
      Nat.card (GaussianOmnificInteger.{u} ⧸ I) = d.norm.natAbs ∧
      Nonempty ((GaussianOmnificInteger.{u} ⧸ I) ≃+* GaussianInt ⧸ Ideal.span {d}) := by
  rcases gaussianOmnific_small_quotient_kernel_cases I with hI | ⟨d, hd, hI⟩
  · exact Or.inl ⟨hI, ⟨(Ideal.quotEquivOfEq hI).trans
      (gaussianOmnificConstantCoeff.quotientKerEquivOfSurjective
        gaussianOmnificConstantCoeff_surjective)⟩⟩
  · subst I
    exact Or.inr ⟨d, hd, rfl, gaussianOmnific_quotient_finite d hd,
      gaussianOmnific_quotient_card d hd, ⟨gaussianOmnificQuotientConstantEquiv d hd⟩⟩

end
end Surreal.Surcomplex
