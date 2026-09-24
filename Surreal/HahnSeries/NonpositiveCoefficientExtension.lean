import Surreal.HahnSeries.NonpositiveSupport
import Surreal.HahnSeries.CoefficientMapping

/-!
# Coefficient extension of support-restricted Hahn rings

The coefficient-extension step of `odg:dec:thm:etale` and
`odg:def:sub:setting`. Injective coefficient maps preserve the full support,
commute with constants and constant extraction, and reflect constancy.
-/

namespace Surreal.HahnSeries

open _root_.HahnSeries

noncomputable section

variable {Γ R S : Type*} [AddCommGroup Γ] [LinearOrder Γ] [IsOrderedAddMonoid Γ]
  [CommRing R] [CommRing S]

/-- A coefficient homomorphism restricts to the nonpositive-support subrings. -/
def nonpositiveMapCoefficients (φ : R →+* S) :
    nonpositiveSupportSubring Γ R →+* nonpositiveSupportSubring Γ S :=
  ((mapCoefficients φ).comp (nonpositiveSupportSubring Γ R).subtype).codRestrict _ (by
    intro f a ha
    change φ (f.val.coeff a) = 0
    rw [f.property a ha, map_zero])

@[simp] theorem coeff_nonpositiveMapCoefficients (φ : R →+* S)
    (f : nonpositiveSupportSubring Γ R) (a : Γ) :
    (nonpositiveMapCoefficients φ f).val.coeff a = φ (f.val.coeff a) := rfl

/-- Coefficient extension commutes with constant extraction. -/
@[simp] theorem nonpositiveConstantCoeff_map (φ : R →+* S)
    (f : nonpositiveSupportSubring Γ R) :
    nonpositiveConstantCoeff (nonpositiveMapCoefficients φ f) = φ (nonpositiveConstantCoeff f) := rfl

/-- Coefficient extension sends constants to their images. -/
@[simp] theorem nonpositiveMapCoefficients_constants (φ : R →+* S) (r : R) :
    nonpositiveMapCoefficients (Γ := Γ) φ (nonpositiveConstants r) =
      nonpositiveConstants (φ r) := by
  apply Subtype.ext
  change mapCoefficients φ (_root_.HahnSeries.C r) = _root_.HahnSeries.C (φ r)
  exact mapCoefficients_single φ 0 r

/-- An injective coefficient map gives an injective map of the support rings. -/
theorem nonpositiveMapCoefficients_injective (φ : R →+* S) (hφ : Function.Injective φ) :
    Function.Injective (nonpositiveMapCoefficients (Γ := Γ) φ) := by
  intro f g h
  apply Subtype.ext
  apply _root_.HahnSeries.ext
  funext a
  apply hφ
  exact congrArg (fun f : nonpositiveSupportSubring Γ S => f.val.coeff a) h

/-- Every coefficient, and therefore the entire support, survives injective extension. -/
theorem support_nonpositiveMapCoefficients (φ : R →+* S) (hφ : Function.Injective φ)
    (f : nonpositiveSupportSubring Γ R) :
    (nonpositiveMapCoefficients φ f).val.support = f.val.support := by
  ext a
  change φ (f.val.coeff a) ≠ 0 ↔ f.val.coeff a ≠ 0
  rw [map_ne_zero_iff φ hφ]

/-- A series becomes constant after injective coefficient extension exactly when it was
already constant, with the specified constant coefficient. -/
theorem nonpositiveMapCoefficients_eq_constant_iff (φ : R →+* S) (hφ : Function.Injective φ)
    (f : nonpositiveSupportSubring Γ R) (c : S) :
    nonpositiveMapCoefficients φ f = nonpositiveConstants c ↔
      f = nonpositiveConstants (nonpositiveConstantCoeff f) ∧ φ (nonpositiveConstantCoeff f) = c := by
  constructor
  · intro h
    have hc := congrArg nonpositiveConstantCoeff h
    simp only [nonpositiveConstantCoeff_map, nonpositiveConstantCoeff_constants] at hc
    refine ⟨?_, hc⟩
    apply nonpositiveMapCoefficients_injective φ hφ
    rw [nonpositiveMapCoefficients_constants, hc]
    exact h
  · rintro ⟨hf, hc⟩
    rw [hf, nonpositiveMapCoefficients_constants, hc]

end
end Surreal.HahnSeries
