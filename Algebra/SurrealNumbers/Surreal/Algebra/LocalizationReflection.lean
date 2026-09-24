import Surreal.Algebra.QuotientReflection
import Mathlib.RingTheory.Localization.Basic

/-!
# Localization preserves small-ring reflection

The algebraic mechanism in `osq:thm:localization`. A surjective ring map
that represents small commutative target maps continues to represent
small target maps after localizing a submonoid and its image. Targets may
be noncommutative: factor through the commutative range of the given map
before applying Mathlib's localization lift. No size bound on the
localized source or its denominator submonoid is assumed.
-/

universe u v w t
namespace Surreal.LocalizationReflection
noncomputable section
variable {A : Type v} {D : Type w} [CommRing A] [CommRing D]

/-- Localization of a map at a submonoid and its image. -/
def reflection (q : A →+* D) (M : Submonoid A) :
    Localization M →+* Localization (M.map q) :=
  IsLocalization.map _ q M.le_comap_map

@[simp] theorem reflection_algebraMap (q : A →+* D) (M : Submonoid A) (a : A) :
    reflection q M (algebraMap A (Localization M) a) =
      algebraMap D (Localization (M.map q)) (q a) :=
  IsLocalization.map_eq _ _

/-- On fractions the localized reflection maps numerator and denominator by q. -/
theorem reflection_mk' (q : A →+* D) (M : Submonoid A) (a : A) (m : M) :
    reflection q M (IsLocalization.mk' (Localization M) a m) =
      IsLocalization.mk' (Localization (M.map q)) (q a) (⟨q m, ⟨m, m.property, rfl⟩⟩ : M.map q) :=
  IsLocalization.map_mk' _ _ _

/-- A surjective reflection remains surjective after localization. -/
theorem reflection_surjective (q : A →+* D) (hq : Function.Surjective q) (M : Submonoid A) :
    Function.Surjective (reflection q M) :=
  IsLocalization.map_surjective_of_surjective M (Localization M) _ hq

variable (q : A →+* D) (hq : Function.Surjective q) (M : Submonoid A)
  (hfactor : ∀ (T : Type t) [CommRing T] [Small.{u} T] (φ : A →+* T),
    ∃ ψ : D →+* T, ψ.comp q = φ)

include hq hfactor in
/-- Small-ring factorization survives localization, even for noncommutative targets. -/
theorem factors {B : Type t} [Ring B] [Small.{u} B] (φ : Localization M →+* B) :
    ∃! ψ : Localization (M.map q) →+* B, ψ.comp (reflection q M) = φ := by
  letI : CommRing φ.range := { (inferInstance : Ring φ.range) with
    mul_comm x y := by
      obtain ⟨a, rfl⟩ := φ.rangeRestrict_surjective x
      obtain ⟨b, rfl⟩ := φ.rangeRestrict_surjective y
      rw [← map_mul, ← map_mul, mul_comm a b] }
  obtain ⟨g, hg⟩ := hfactor φ.range (φ.rangeRestrict.comp (algebraMap A (Localization M)))
  have hu (m : M.map q) : IsUnit (g m) := by
    obtain ⟨a, ha, he⟩ := m.property
    have h := RingHom.congr_fun hg a
    change g (q a) = φ.rangeRestrict (algebraMap A (Localization M) a) at h
    rw [← he, h]
    exact (IsLocalization.map_units (Localization M) (⟨a, ha⟩ : M)).map φ.rangeRestrict
  let ψ : Localization (M.map q) →+* B := φ.range.subtype.comp (IsLocalization.lift hu)
  have hψ : ψ.comp (reflection q M) = φ := by
    apply IsLocalization.ringHom_ext M
    apply RingHom.ext
    intro a
    change φ.range.subtype (IsLocalization.lift hu
      (reflection q M (algebraMap A (Localization M) a))) = φ (algebraMap A (Localization M) a)
    rw [reflection_algebraMap, IsLocalization.lift_eq]
    exact congrArg Subtype.val (RingHom.congr_fun hg a)
  refine ⟨ψ, hψ, ?_⟩
  intro ψ' hψ'
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := reflection_surjective q hq M x
  exact (RingHom.congr_fun hψ' y).trans (RingHom.congr_fun hψ y).symm

/-- Maps from a localization to small rings are maps from its localized reflection. -/
def homEquiv (B : Type t) [Ring B] [Small.{u} B] :
    (Localization M →+* B) ≃ (Localization (M.map q) →+* B) where
  toFun φ := (factors q hq M hfactor φ).choose
  invFun ψ := ψ.comp (reflection q M)
  left_inv φ := (factors q hq M hfactor φ).choose_spec.1
  right_inv ψ := ((factors q hq M hfactor (ψ.comp (reflection q M))).choose_spec.2 ψ rfl).symm

/-- The inverse correspondence is precomposition with the canonical localized reflection. -/
theorem homEquiv_symm_apply (B : Type t) [Ring B] [Small.{u} B]
    (ψ : Localization (M.map q) →+* B) :
    (homEquiv q hq M hfactor B).symm ψ = ψ.comp (reflection q M) := rfl

/-- The factorization reconstructs the original map on every localized element. -/
theorem homEquiv_comp (B : Type t) [Ring B] [Small.{u} B] (φ : Localization M →+* B) :
    (homEquiv q hq M hfactor B φ).comp (reflection q M) = φ :=
  (factors q hq M hfactor φ).choose_spec.1

/-- Mapping a fraction multiplies the numerator image by the unit inverse of its denominator. -/
theorem map_mk'_formula {B : Type t} [Ring B] (φ : Localization M →+* B) (a : A) (m : M) :
    φ (IsLocalization.mk' (Localization M) a m) =
      φ (algebraMap A (Localization M) a) * Ring.inverse (φ (algebraMap A (Localization M) m)) := by
  have hu := (IsLocalization.map_units (Localization M) m).map φ
  calc
    φ (IsLocalization.mk' (Localization M) a m) =
        φ (IsLocalization.mk' (Localization M) a m) *
          (φ (algebraMap A (Localization M) m) * Ring.inverse (φ (algebraMap A (Localization M) m))) := by
      rw [Ring.mul_inverse_cancel _ hu, mul_one]
    _ = φ (algebraMap A (Localization M) a) *
        Ring.inverse (φ (algebraMap A (Localization M) m)) := by
      rw [← mul_assoc, ← map_mul, IsLocalization.mk'_spec]

/-- Inverting zero in the ordinary reflection gives the zero ring. -/
theorem reflected_subsingleton (h0 : (0 : D) ∈ M.map q) :
    Subsingleton (Localization (M.map q)) := IsLocalization.subsingleton h0

include hq hfactor in
/-- If a denominator has zero reflected value, there is no nonzero small unital target. -/
theorem no_small_hom_of_zero_mem {B : Type t} [Ring B] [Nontrivial B] [Small.{u} B]
    (h0 : (0 : D) ∈ M.map q) : ¬ Nonempty (Localization M →+* B) := by
  rintro ⟨φ⟩
  obtain ⟨ψ, _, _⟩ := factors q hq M hfactor φ
  letI := reflected_subsingleton q M h0
  have h : (1 : B) = 0 := by
    rw [← map_one ψ, Subsingleton.elim (1 : Localization (M.map q)) 0, map_zero]
  exact one_ne_zero h

end
end Surreal.LocalizationReflection
