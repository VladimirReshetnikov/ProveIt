import Surreal.Surcomplex.GaussianSmallTargets
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.GroupWithZero.Action.Units

/-!
# No small targets after inverting a purely infinite element

The actual real and Gaussian clauses of `osq:cor:nofield` and
`osq:prop:fractions`(iv). The obstruction applies to any ring extension in
which a purely infinite element is a unit, including native localizations
and the actual surreal and surcomplex fields. The module argument acts on
each vector directly, without passing to an endomorphism ring.
-/

universe u v w
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Inverting one infinite element excludes every nonzero small unital ring image. -/
theorem omnific_unit_extension_no_small_hom {B : Type v} [Ring B]
    (ι : OmnificInteger.{u} →+* B) (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal)
    (hu : IsUnit (ι x)) (S : Type w) [Ring S] [Nontrivial S] [Small.{u} S] :
    ¬ Nonempty (B →+* S) := by
  rintro ⟨φ⟩
  exact (hu.map φ).ne_zero (omnific_small_hom_purelyInfinite (φ.comp ι).toNonUnitalRingHom x hx)

/-- Inverting one infinite element also makes every small unital module trivial. -/
theorem omnific_unit_extension_small_module {B : Type v} [Ring B]
    (ι : OmnificInteger.{u} →+* B) (x : OmnificInteger.{u}) (hx : x ∈ omnificPurelyInfiniteIdeal)
    (hu : IsUnit (ι x)) (M : Type w) [AddCommGroup M] [Module B M] [Small.{u} M] :
    Subsingleton M := by
  letI : Module OmnificInteger.{u} M := Module.compHom M ι
  have hz (m : M) : m = 0 := hu.smul_eq_zero.mp (omnific_purelyInfinite_smul_small x hx m)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Native localization away from an infinite element has no nonzero small ring target. -/
theorem omnific_localization_no_small_hom (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (B : Type v) [CommRing B]
    [Algebra OmnificInteger.{u} B] [IsLocalization.Away x B]
    (S : Type w) [Ring S] [Nontrivial S] [Small.{u} S] : ¬ Nonempty (B →+* S) :=
  omnific_unit_extension_no_small_hom (algebraMap OmnificInteger.{u} B) x hx
    (IsLocalization.Away.algebraMap_isUnit x) S

/-- Native localization away from an infinite element has no nonzero small module. -/
theorem omnific_localization_small_module (x : OmnificInteger.{u})
    (hx : x ∈ omnificPurelyInfiniteIdeal) (B : Type v) [CommRing B]
    [Algebra OmnificInteger.{u} B] [IsLocalization.Away x B]
    (M : Type w) [AddCommGroup M] [Module B M] [Small.{u} M] : Subsingleton M :=
  omnific_unit_extension_small_module (algebraMap OmnificInteger.{u} B) x hx
    (IsLocalization.Away.algebraMap_isUnit x) M

/-- The actual surreal field has no nonzero small unital ring image. -/
theorem surreal_no_small_ringHom (S : Type v) [Ring S] [Nontrivial S] [Small.{u} S] :
    ¬ Nonempty (SignSequence.{u} →+* S) :=
  omnific_unit_extension_no_small_hom omnificToSurreal (omnificMonomial 1 zero_lt_one)
    (omnificMonomial_mem_purelyInfinite 1 zero_lt_one)
    (isUnit_iff_ne_zero.mpr (omegaPower_ne_zero 1)) S

/-- Every small module over the actual surreal field is trivial. -/
theorem surreal_small_module (M : Type v) [AddCommGroup M] [Module SignSequence.{u} M]
    [Small.{u} M] : Subsingleton M :=
  omnific_unit_extension_small_module omnificToSurreal (omnificMonomial 1 zero_lt_one)
    (omnificMonomial_mem_purelyInfinite 1 zero_lt_one)
    (isUnit_iff_ne_zero.mpr (omegaPower_ne_zero 1)) M

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- A Gaussian extension inverting an infinite element has no nonzero small unital ring image. -/
theorem gaussianOmnific_unit_extension_no_small_hom {B : Type v} [Ring B]
    (ι : GaussianOmnificInteger.{u} →+* B) (x : GaussianOmnificInteger.{u})
    (hx : x ∈ gaussianOmnificPurelyInfiniteIdeal) (hu : IsUnit (ι x))
    (S : Type w) [Ring S] [Nontrivial S] [Small.{u} S] : ¬ Nonempty (B →+* S) := by
  rintro ⟨φ⟩
  exact (hu.map φ).ne_zero
    (gaussianOmnific_small_hom_purelyInfinite (φ.comp ι).toNonUnitalRingHom x hx)

/-- A Gaussian extension inverting an infinite element has only trivial small modules. -/
theorem gaussianOmnific_unit_extension_small_module {B : Type v} [Ring B]
    (ι : GaussianOmnificInteger.{u} →+* B) (x : GaussianOmnificInteger.{u})
    (hx : x ∈ gaussianOmnificPurelyInfiniteIdeal) (hu : IsUnit (ι x))
    (M : Type w) [AddCommGroup M] [Module B M] [Small.{u} M] : Subsingleton M := by
  letI : Module GaussianOmnificInteger.{u} M := Module.compHom M ι
  have hz (m : M) : m = 0 := hu.smul_eq_zero.mp (gaussianOmnific_purelyInfinite_smul_small x hx m)
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- Every Gaussian localization away from an infinite element excludes nonzero small ring images. -/
theorem gaussianOmnific_localization_no_small_hom (x : GaussianOmnificInteger.{u})
    (hx : x ∈ gaussianOmnificPurelyInfiniteIdeal) (B : Type v) [CommRing B]
    [Algebra GaussianOmnificInteger.{u} B] [IsLocalization.Away x B]
    (S : Type w) [Ring S] [Nontrivial S] [Small.{u} S] : ¬ Nonempty (B →+* S) :=
  gaussianOmnific_unit_extension_no_small_hom (algebraMap GaussianOmnificInteger.{u} B) x hx
    (IsLocalization.Away.algebraMap_isUnit x) S

/-- Every Gaussian localization away from an infinite element has only trivial small modules. -/
theorem gaussianOmnific_localization_small_module (x : GaussianOmnificInteger.{u})
    (hx : x ∈ gaussianOmnificPurelyInfiniteIdeal) (B : Type v) [CommRing B]
    [Algebra GaussianOmnificInteger.{u} B] [IsLocalization.Away x B]
    (M : Type w) [AddCommGroup M] [Module B M] [Small.{u} M] : Subsingleton M :=
  gaussianOmnific_unit_extension_small_module (algebraMap GaussianOmnificInteger.{u} B) x hx
    (IsLocalization.Away.algebraMap_isUnit x) M

/-- The actual surcomplex field has no nonzero small unital ring image. -/
theorem surcomplex_no_small_ringHom (S : Type v) [Ring S] [Nontrivial S] [Small.{u} S] :
    ¬ Nonempty (Surcomplex.{u} →+* S) := by
  rintro ⟨φ⟩
  exact SignSequence.surreal_no_small_ringHom S ⟨φ.comp ofReal⟩

/-- Every small module over the actual surcomplex field is trivial. -/
theorem surcomplex_small_module (M : Type v) [AddCommGroup M] [Module Surcomplex.{u} M]
    [Small.{u} M] : Subsingleton M := by
  letI : Module SignSequence.{u} M := Module.compHom M ofReal
  exact SignSequence.surreal_small_module M

end
end Surreal.Surcomplex
