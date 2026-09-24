import Surreal.Algebra.LocalizationReflection
import Surreal.Foundations.OmnificSmallQuotients
import Surreal.Surcomplex.GaussianSmallQuotients

/-!
# Localized quotients and their ordinary constant reflections

The actual real and Gaussian instances of `osq:thm:localization`.
The denominator submonoid may be arbitrarily large; the target is small
in the birthday universe and may be noncommutative. The constructions
use native quotients and localizations, including zero rings.
-/

universe u v
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- The native localization of an omnific quotient at the images of specified denominators. -/
abbrev OmnificLocalizedQuotient (I : Ideal OmnificInteger.{u}) (M : Submonoid OmnificInteger.{u}) :=
  Localization (M.map (Ideal.Quotient.mk I))

/-- The ordinary localized quotient determined by the constant terms of the ideal and denominators. -/
abbrev OmnificLocalizedConstantQuotient (I : Ideal OmnificInteger.{u}) (M : Submonoid OmnificInteger.{u}) :=
  Localization ((M.map (Ideal.Quotient.mk I)).map (omnificQuotientReflection I))

/-- The canonical quotient-localization map sends numerators and denominators to their constants. -/
def omnificLocalizedQuotientReflection (I : Ideal OmnificInteger.{u}) (M : Submonoid OmnificInteger.{u}) :
    OmnificLocalizedQuotient I M →+* OmnificLocalizedConstantQuotient I M :=
  LocalizationReflection.reflection (omnificQuotientReflection I) (M.map (Ideal.Quotient.mk I))

/-- The localized constant reflection is onto, even when its source is large. -/
theorem omnificLocalizedQuotientReflection_surjective
    (I : Ideal OmnificInteger.{u}) (M : Submonoid OmnificInteger.{u}) :
    Function.Surjective (omnificLocalizedQuotientReflection I M) :=
  LocalizationReflection.reflection_surjective _
    (QuotientReflection.reflection_surjective omnificConstantCoeff omnificConstantCoeff_surjective I) _

/-- All small unital maps from a localized quotient factor uniquely through its constant localization. -/
def omnificLocalizedQuotientSmallHomEquiv
    (I : Ideal OmnificInteger.{u}) (M : Submonoid OmnificInteger.{u}) (B : Type v)
    [Ring B] [Small.{u} B] :
    (OmnificLocalizedQuotient I M →+* B) ≃ (OmnificLocalizedConstantQuotient I M →+* B) :=
  LocalizationReflection.homEquiv (omnificQuotientReflection I)
    (QuotientReflection.reflection_surjective omnificConstantCoeff omnificConstantCoeff_surjective I)
    (M.map (Ideal.Quotient.mk I))
    (fun T _ _ φ => ⟨omnificQuotientSmallHomEquiv I T φ,
      (omnificQuotientSmallHomEquiv I T).symm_apply_apply φ⟩) B

/-- The inverse correspondence is precomposition with the canonical localized reflection. -/
theorem omnificLocalizedQuotientSmallHomEquiv_symm
    (I : Ideal OmnificInteger.{u}) (M : Submonoid OmnificInteger.{u}) (B : Type v)
    [Ring B] [Small.{u} B] (ψ : OmnificLocalizedConstantQuotient I M →+* B) :
    (omnificLocalizedQuotientSmallHomEquiv I M B).symm ψ =
      ψ.comp (omnificLocalizedQuotientReflection I M) := rfl

/-- A denominator whose constant lies in the constant ideal leaves no nonzero small ring image. -/
theorem omnificLocalizedQuotient_no_small_hom
    (I : Ideal OmnificInteger.{u}) (M : Submonoid OmnificInteger.{u})
    {s : OmnificInteger.{u}} (hs : s ∈ M) (hct : omnificConstantCoeff s ∈ I.map omnificConstantCoeff)
    (B : Type v) [Ring B] [Nontrivial B] [Small.{u} B] :
    ¬ Nonempty (OmnificLocalizedQuotient I M →+* B) := by
  have h0 : (0 : ℤ ⧸ I.map omnificConstantCoeff) ∈
      (M.map (Ideal.Quotient.mk I)).map (omnificQuotientReflection I) :=
    ⟨Ideal.Quotient.mk I s, ⟨s, hs, rfl⟩, Ideal.Quotient.eq_zero_iff_mem.mpr hct⟩
  letI : Subsingleton (OmnificLocalizedConstantQuotient I M) :=
    LocalizationReflection.reflected_subsingleton _ _ h0
  rintro ⟨φ⟩
  let ψ := omnificLocalizedQuotientSmallHomEquiv I M B φ
  exact one_ne_zero (show (1 : B) = 0 by
    rw [← map_one ψ, Subsingleton.elim (1 : OmnificLocalizedConstantQuotient I M) 0, map_zero])

/-- In arbitrary noncommutative small targets, a localized fraction has the integer constant formula. -/
theorem omnificLocalizedQuotient_fraction_formula
    (I : Ideal OmnificInteger.{u}) (M : Submonoid OmnificInteger.{u})
    {B : Type v} [Ring B] [Small.{u} B] (φ : OmnificLocalizedQuotient I M →+* B)
    (f : OmnificInteger.{u}) (s : M) :
    φ (IsLocalization.mk' (OmnificLocalizedQuotient I M) (Ideal.Quotient.mk I f)
      (⟨Ideal.Quotient.mk I s, ⟨s, s.property, rfl⟩⟩ : M.map (Ideal.Quotient.mk I))) =
      (omnificConstantCoeff f : B) * Ring.inverse (omnificConstantCoeff s : B) := by
  rw [LocalizationReflection.map_mk'_formula]
  have h (a : OmnificInteger.{u}) := omnific_small_ringHom_eq_constant
    ((φ.comp (algebraMap _ (OmnificLocalizedQuotient I M))).comp (Ideal.Quotient.mk I)) a
  change ∀ a, φ (algebraMap _ _ (Ideal.Quotient.mk I a)) = (omnificConstantCoeff a : B) at h
  rw [h, h]

/-- The quotient-free localization correspondence uses the image of the original denominator monoid. -/
def omnificLocalizationSmallHomEquiv (M : Submonoid OmnificInteger.{u}) (B : Type v)
    [Ring B] [Small.{u} B] :
    (Localization M →+* B) ≃ (Localization (M.map omnificConstantCoeff) →+* B) :=
  LocalizationReflection.homEquiv omnificConstantCoeff omnificConstantCoeff_surjective M
    (fun T _ _ φ => ⟨omnificSmallRingHomEquiv T φ, (omnificSmallRingHomEquiv T).symm_apply_apply φ⟩) B

/-- Inverting one arbitrary element has ordinary reflection given by inverting its constant. -/
def omnificAwaySmallHomEquiv (s : OmnificInteger.{u}) (B : Type v) [Ring B] [Small.{u} B] :
    (Localization.Away s →+* B) ≃ (Localization.Away (omnificConstantCoeff s) →+* B) := by
  have he : (Submonoid.powers s).map omnificConstantCoeff =
      Submonoid.powers (omnificConstantCoeff s) := Submonoid.map_powers _ _
  change (Localization (Submonoid.powers s) →+* B) ≃
    (Localization (Submonoid.powers (omnificConstantCoeff s)) →+* B)
  rw [← he]
  exact omnificLocalizationSmallHomEquiv (Submonoid.powers s) B

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- The native localization of a Gaussian omnific quotient at the images of specified denominators. -/
abbrev GaussianOmnificLocalizedQuotient (I : Ideal GaussianOmnificInteger.{u}) (M : Submonoid GaussianOmnificInteger.{u}) :=
  Localization (M.map (Ideal.Quotient.mk I))

/-- The ordinary Gaussian localized quotient determined by the constant terms of the ideal and denominators. -/
abbrev GaussianOmnificLocalizedConstantQuotient (I : Ideal GaussianOmnificInteger.{u}) (M : Submonoid GaussianOmnificInteger.{u}) :=
  Localization ((M.map (Ideal.Quotient.mk I)).map (gaussianOmnificQuotientReflection I))

/-- The canonical quotient-localization map sends numerators and denominators to their constants. -/
def gaussianOmnificLocalizedQuotientReflection (I : Ideal GaussianOmnificInteger.{u}) (M : Submonoid GaussianOmnificInteger.{u}) :
    GaussianOmnificLocalizedQuotient I M →+* GaussianOmnificLocalizedConstantQuotient I M :=
  LocalizationReflection.reflection (gaussianOmnificQuotientReflection I) (M.map (Ideal.Quotient.mk I))

/-- The localized constant reflection is onto, even when its source is large. -/
theorem gaussianOmnificLocalizedQuotientReflection_surjective
    (I : Ideal GaussianOmnificInteger.{u}) (M : Submonoid GaussianOmnificInteger.{u}) :
    Function.Surjective (gaussianOmnificLocalizedQuotientReflection I M) :=
  LocalizationReflection.reflection_surjective _
    (QuotientReflection.reflection_surjective gaussianOmnificConstantCoeff.{u} gaussianOmnificConstantCoeff_surjective I) _

/-- All small unital maps from a localized quotient factor uniquely through its constant localization. -/
def gaussianOmnificLocalizedQuotientSmallHomEquiv
    (I : Ideal GaussianOmnificInteger.{u}) (M : Submonoid GaussianOmnificInteger.{u}) (B : Type v)
    [Ring B] [Small.{u} B] :
    (GaussianOmnificLocalizedQuotient I M →+* B) ≃ (GaussianOmnificLocalizedConstantQuotient I M →+* B) :=
  LocalizationReflection.homEquiv (gaussianOmnificQuotientReflection I)
    (QuotientReflection.reflection_surjective gaussianOmnificConstantCoeff.{u} gaussianOmnificConstantCoeff_surjective I)
    (M.map (Ideal.Quotient.mk I))
    (fun T _ _ φ => ⟨gaussianOmnificQuotientSmallHomEquiv I T φ,
      (gaussianOmnificQuotientSmallHomEquiv I T).symm_apply_apply φ⟩) B

/-- The inverse correspondence is precomposition with the canonical localized reflection. -/
theorem gaussianOmnificLocalizedQuotientSmallHomEquiv_symm
    (I : Ideal GaussianOmnificInteger.{u}) (M : Submonoid GaussianOmnificInteger.{u}) (B : Type v)
    [Ring B] [Small.{u} B] (ψ : GaussianOmnificLocalizedConstantQuotient I M →+* B) :
    (gaussianOmnificLocalizedQuotientSmallHomEquiv I M B).symm ψ =
      ψ.comp (gaussianOmnificLocalizedQuotientReflection I M) := rfl

/-- A denominator whose constant lies in the constant ideal leaves no nonzero small ring image. -/
theorem gaussianOmnificLocalizedQuotient_no_small_hom
    (I : Ideal GaussianOmnificInteger.{u}) (M : Submonoid GaussianOmnificInteger.{u})
    {s : GaussianOmnificInteger.{u}} (hs : s ∈ M) (hct : gaussianOmnificConstantCoeff.{u} s ∈ I.map gaussianOmnificConstantCoeff.{u})
    (B : Type v) [Ring B] [Nontrivial B] [Small.{u} B] :
    ¬ Nonempty (GaussianOmnificLocalizedQuotient I M →+* B) := by
  have h0 : (0 : GaussianInt ⧸ I.map gaussianOmnificConstantCoeff.{u}) ∈
      (M.map (Ideal.Quotient.mk I)).map (gaussianOmnificQuotientReflection I) :=
    ⟨Ideal.Quotient.mk I s, ⟨s, hs, rfl⟩, Ideal.Quotient.eq_zero_iff_mem.mpr hct⟩
  letI : Subsingleton (GaussianOmnificLocalizedConstantQuotient I M) :=
    LocalizationReflection.reflected_subsingleton _ _ h0
  rintro ⟨φ⟩
  let ψ := gaussianOmnificLocalizedQuotientSmallHomEquiv I M B φ
  exact one_ne_zero (show (1 : B) = 0 by
    rw [← map_one ψ, Subsingleton.elim (1 : GaussianOmnificLocalizedConstantQuotient I M) 0, map_zero])

/-- The quotient-free localization correspondence uses the image of the original denominator monoid. -/
def gaussianOmnificLocalizationSmallHomEquiv (M : Submonoid GaussianOmnificInteger.{u}) (B : Type v)
    [Ring B] [Small.{u} B] :
    (Localization M →+* B) ≃ (Localization (M.map gaussianOmnificConstantCoeff.{u}) →+* B) :=
  LocalizationReflection.homEquiv gaussianOmnificConstantCoeff.{u} gaussianOmnificConstantCoeff_surjective M
    (fun T _ _ φ => ⟨gaussianOmnificSmallRingHomEquiv.{u} T φ, (gaussianOmnificSmallRingHomEquiv.{u} T).symm_apply_apply φ⟩) B

/-- Inverting one arbitrary element has ordinary reflection given by inverting its constant. -/
def gaussianOmnificAwaySmallHomEquiv (s : GaussianOmnificInteger.{u}) (B : Type v) [Ring B] [Small.{u} B] :
    (Localization.Away s →+* B) ≃ (Localization.Away (gaussianOmnificConstantCoeff.{u} s) →+* B) := by
  have he : (Submonoid.powers s).map gaussianOmnificConstantCoeff.{u} =
      Submonoid.powers (gaussianOmnificConstantCoeff.{u} s) := Submonoid.map_powers _ _
  change (Localization (Submonoid.powers s) →+* B) ≃
    (Localization (Submonoid.powers (gaussianOmnificConstantCoeff.{u} s)) →+* B)
  rw [← he]
  exact gaussianOmnificLocalizationSmallHomEquiv.{u} (Submonoid.powers s) B

end
end Surreal.Surcomplex
