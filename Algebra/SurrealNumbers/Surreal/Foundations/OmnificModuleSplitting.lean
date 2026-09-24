import Surreal.Surcomplex.SmallModuleCorrespondence
import Mathlib.LinearAlgebra.FreeModule.Basic

/-!
# Small-module projectivity and the nonsplit constant sequence

The full actual-ring statements `osq:prop:nonsplit` and
`osq:rep:prop:projectivity`. Constant extraction is a surjective linear map
with purely infinite kernel and a ring section, but it has no omnific-linear
section. Projectivity of the integers is expressed by lifting against
surjections between small modules; it is not unrestricted module projectivity.
The following assertion that nonzero free modules are not small is also proved.
-/

universe u v w
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- The integer module inflated along the constant coefficient. -/
abbrev omnificIntegerConstantModule : Module OmnificInteger.{u} ℤ :=
  Module.compHom ℤ omnificConstantCoeff

attribute [local instance] omnificIntegerConstantModule

/-- Constant extraction as a linear map to the inflated integer module. -/
def omnificConstantLinearMap : OmnificInteger.{u} →ₗ[OmnificInteger.{u}] ℤ where
  toAddHom := omnificConstantCoeff.toAddHom
  map_smul' a x := map_mul omnificConstantCoeff a x

/-- The purely infinite inclusion and constant extraction form an exact pair. -/
theorem omnific_constant_sequence_exact :
    Function.Exact omnificPurelyInfiniteIdeal.{u}.subtype omnificConstantLinearMap.{u} := by
  intro x
  constructor
  · intro hx
    exact ⟨⟨x, hx⟩, rfl⟩
  · rintro ⟨x, rfl⟩
    exact x.property

/-- The left map of the constant sequence is injective. -/
theorem omnific_constant_sequence_injective :
    Function.Injective omnificPurelyInfiniteIdeal.{u}.subtype := Subtype.val_injective

/-- The right map of the constant sequence is surjective. -/
theorem omnific_constant_sequence_surjective :
    Function.Surjective omnificConstantLinearMap.{u} := omnificConstantCoeff_surjective

/-- Every map from a small omnific module to the regular module is zero. -/
theorem omnific_small_linearMap_to_regular_eq_zero {M : Type v} [AddCommGroup M]
    [Module OmnificInteger.{u} M] [Small.{u} M] (f : M →ₗ[OmnificInteger.{u}] OmnificInteger.{u}) :
    f = 0 := by
  apply LinearMap.ext
  intro m
  have he := f.map_smul (omnificMonomial (1 : SignSequence.{u}) zero_lt_one) m
  rw [omnific_monomial_smul_small, map_zero] at he
  exact (mul_eq_zero.mp he.symm).resolve_left (omnificMonomial_ne_zero _ _)

/-- The constant sequence has no omnific-linear section. -/
theorem omnific_constant_sequence_nonsplit :
    ¬ ∃ s : ℤ →ₗ[OmnificInteger.{u}] OmnificInteger.{u},
      omnificConstantLinearMap.comp s = LinearMap.id := by
  rintro ⟨s, hs⟩
  have he := LinearMap.congr_fun hs 1
  rw [omnific_small_linearMap_to_regular_eq_zero s] at he
  change omnificConstantCoeff 0 = 1 at he
  simp at he

/-- Integer inclusion is nevertheless a ring section, and hence an additive section. -/
theorem omnific_constant_sequence_ring_section :
    omnificConstantCoeff.{u}.comp omnificIntCast = RingHom.id ℤ := by
  ext n
  exact omnificConstantCoeff_intCast n

/-- Projectivity within small modules: every map from the integers lifts through a surjection. -/
theorem omnific_integer_small_projective {M : Type v} {N : Type w}
    [AddCommGroup M] [AddCommGroup N]
    [Module OmnificInteger.{u} M] [Module OmnificInteger.{u} N] [Small.{u} M] [Small.{u} N]
    (g : M →ₗ[OmnificInteger.{u}] N) (hg : Function.Surjective g)
    (h : ℤ →ₗ[OmnificInteger.{u}] N) :
    ∃ f : ℤ →ₗ[OmnificInteger.{u}] M, g.comp f = h := by
  obtain ⟨m, hm⟩ := hg (h 1)
  let f : ℤ →+ M :=
    { toFun := fun n => n • m
      map_zero' := zero_zsmul m
      map_add' := fun a b => add_zsmul m a b }
  refine ⟨(omnificSmallLinearMapEquiv ℤ M).symm f, ?_⟩
  apply LinearMap.ext
  intro n
  change g (n • m) = h n
  rw [map_zsmul, hm]
  simpa using (map_zsmul h n (1 : ℤ)).symm

/-- A nonzero free omnific module cannot be small in the birthday universe. -/
theorem omnific_nontrivial_free_module_not_small (M : Type v) [AddCommGroup M]
    [Module OmnificInteger.{u} M] [Module.Free OmnificInteger.{u} M] [Nontrivial M] :
    ¬ Small.{u} M := by
  intro hs
  letI := hs
  apply omnificMonomial_ne_zero (1 : SignSequence.{u}) zero_lt_one
  exact eq_of_smul_eq_smul (fun m : M => by
    rw [omnific_monomial_smul_small, _root_.zero_smul])

end
end Surreal.Foundations.SignSequence
