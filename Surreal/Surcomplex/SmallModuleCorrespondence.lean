import Surreal.Algebra.ModuleReflection
import Surreal.Surcomplex.GaussianSmallTargets

/-!
# Small modules over the actual real and Gaussian omnific integers

The two actual-ring instances of `osq:thm:modules`: restriction to ordinary
constants and inflation along the constant coefficient are inverse on module
structures over a small additive group. Morphisms keep their underlying
functions, and the correspondence preserves identities, composition and
exactness. Smallness is relative to the birthday universe of the source ring.
-/

universe u v w t
namespace Surreal.Foundations.SignSequence
noncomputable section

/-- Every small action is unchanged by the embedded integer constant endomorphism. -/
theorem omnific_smul_small_eq_embedded_constant {M : Type v} [AddCommGroup M]
    [Module OmnificInteger.{u} M] [Small.{u} M] (a : OmnificInteger.{u}) (m : M) :
    a • m = omnificIntCast (omnificConstantCoeff a) • m := by
  rw [omnific_smul_small_eq_constant, omnific_smul_small_eq_constant, omnificConstantCoeff_intCast]

/-- Restriction and inflation identify real omnific and integer module structures on a small group. -/
def omnificSmallModuleEquiv (M : Type v) [AddCommGroup M] [Small.{u} M] :
    Module OmnificInteger.{u} M ≃ Module ℤ M :=
  ModuleReflection.moduleEquiv omnificConstantCoeff omnificIntCast omnificConstantCoeff_intCast M
    (fun P => by
      letI := P
      exact omnific_smul_small_eq_embedded_constant)

/-- Every small abelian group has exactly one real omnific module structure. -/
theorem omnific_small_module_unique (M : Type v) [AddCommGroup M] [Small.{u} M] :
    ∃! _P : Module OmnificInteger.{u} M, True := by
  refine ⟨(omnificSmallModuleEquiv M).symm inferInstance, trivial, ?_⟩
  intro P _
  apply (omnificSmallModuleEquiv M).injective
  exact Subsingleton.elim _ _

/-- Every additive map between small real omnific modules is automatically omnific-linear. -/
def omnificSmallLinearMapEquiv (M : Type v) (N : Type w) [AddCommGroup M] [AddCommGroup N]
    [Module OmnificInteger.{u} M] [Module OmnificInteger.{u} N] [Small.{u} M] [Small.{u} N] :
    (M →ₗ[OmnificInteger.{u}] N) ≃ (M →+ N) where
  toFun f := f.toAddMonoidHom
  invFun g :=
    { g with
      map_smul' := fun a m => by
        rw [omnific_smul_small_eq_constant, omnific_smul_small_eq_constant]
        exact map_zsmul g _ _ }
  left_inv _ := LinearMap.ext (fun _ => rfl)
  right_inv _ := AddMonoidHom.ext (fun _ => rfl)

/-- The real morphism correspondence keeps every value unchanged. -/
theorem omnificSmallLinearMapEquiv_apply (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N] [Module OmnificInteger.{u} M] [Module OmnificInteger.{u} N]
    [Small.{u} M] [Small.{u} N] (f : M →ₗ[OmnificInteger.{u}] N) (m : M) :
    omnificSmallLinearMapEquiv M N f m = f m := rfl

/-- Real restriction preserves identity maps. -/
theorem omnificSmallLinearMapEquiv_id (M : Type v) [AddCommGroup M]
    [Module OmnificInteger.{u} M] [Small.{u} M] :
    omnificSmallLinearMapEquiv M M LinearMap.id = AddMonoidHom.id M := rfl

/-- Real restriction preserves composition. -/
theorem omnificSmallLinearMapEquiv_comp (M : Type v) (N : Type w) (P : Type t)
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module OmnificInteger.{u} M] [Module OmnificInteger.{u} N] [Module OmnificInteger.{u} P]
    [Small.{u} M] [Small.{u} N] [Small.{u} P]
    (f : M →ₗ[OmnificInteger.{u}] N) (g : N →ₗ[OmnificInteger.{u}] P) :
    omnificSmallLinearMapEquiv M P (g.comp f) =
      (omnificSmallLinearMapEquiv N P g).comp (omnificSmallLinearMapEquiv M N f) := rfl

/-- Exact sequences of small real omnific modules are exactly exact sequences of abelian groups. -/
theorem omnificSmallLinearMapEquiv_exact_iff (M : Type v) (N : Type w) (P : Type t)
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module OmnificInteger.{u} M] [Module OmnificInteger.{u} N] [Module OmnificInteger.{u} P]
    [Small.{u} M] [Small.{u} N] [Small.{u} P]
    (f : M →ₗ[OmnificInteger.{u}] N) (g : N →ₗ[OmnificInteger.{u}] P) :
    Function.Exact (omnificSmallLinearMapEquiv M N f) (omnificSmallLinearMapEquiv N P g) ↔
      Function.Exact f g := Iff.rfl

end
end Surreal.Foundations.SignSequence

namespace Surreal.Surcomplex
open Foundations
noncomputable section

/-- Restriction and inflation identify Gaussian omnific and Gaussian integer module structures. -/
def gaussianOmnificSmallModuleEquiv (M : Type v) [AddCommGroup M] [Small.{u} M] :
    Module GaussianOmnificInteger.{u} M ≃ Module GaussianInt M :=
  ModuleReflection.moduleEquiv gaussianOmnificConstantCoeff.{u} gaussianOmnificConstants.{u}
    gaussianOmnificConstantCoeff_constants M (fun P => by
      letI := P
      exact gaussianOmnific_smul_small_eq_constant)

/-- The underlying ordinary Gaussian module of a Gaussian omnific module. -/
abbrev gaussianOmnificRestrictedModule (M : Type v) [AddCommGroup M]
    [Module GaussianOmnificInteger.{u} M] : Module GaussianInt M :=
  Module.compHom M gaussianOmnificConstants.{u}

/-- Gaussian linearity is precisely ordinary Gaussian linearity on the same small groups. -/
def gaussianOmnificSmallLinearMapEquiv (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N]
    [Module GaussianOmnificInteger.{u} M] [Module GaussianOmnificInteger.{u} N]
    [Small.{u} M] [Small.{u} N] :
    (M →ₗ[GaussianOmnificInteger.{u}] N) ≃
      (letI := gaussianOmnificRestrictedModule M; letI := gaussianOmnificRestrictedModule N;
        M →ₗ[GaussianInt] N) :=
  ModuleReflection.linearMapEquiv gaussianOmnificConstantCoeff.{u} gaussianOmnificConstants.{u}
    gaussianOmnific_smul_small_eq_constant gaussianOmnific_smul_small_eq_constant

/-- The Gaussian morphism correspondence keeps every value unchanged. -/
theorem gaussianOmnificSmallLinearMapEquiv_apply (M : Type v) (N : Type w)
    [AddCommGroup M] [AddCommGroup N]
    [Module GaussianOmnificInteger.{u} M] [Module GaussianOmnificInteger.{u} N]
    [Small.{u} M] [Small.{u} N] (f : M →ₗ[GaussianOmnificInteger.{u}] N) (m : M) :
    gaussianOmnificSmallLinearMapEquiv M N f m = f m := rfl

/-- Gaussian restriction preserves identity maps. -/
theorem gaussianOmnificSmallLinearMapEquiv_id (M : Type v) [AddCommGroup M]
    [Module GaussianOmnificInteger.{u} M] [Small.{u} M] :
    gaussianOmnificSmallLinearMapEquiv M M LinearMap.id =
      (letI := gaussianOmnificRestrictedModule M; (LinearMap.id : M →ₗ[GaussianInt] M)) := rfl

/-- Gaussian restriction preserves composition. -/
theorem gaussianOmnificSmallLinearMapEquiv_comp (M : Type v) (N : Type w) (P : Type t)
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module GaussianOmnificInteger.{u} M] [Module GaussianOmnificInteger.{u} N]
    [Module GaussianOmnificInteger.{u} P] [Small.{u} M] [Small.{u} N] [Small.{u} P]
    (f : M →ₗ[GaussianOmnificInteger.{u}] N) (g : N →ₗ[GaussianOmnificInteger.{u}] P) :
    gaussianOmnificSmallLinearMapEquiv M P (g.comp f) =
      (gaussianOmnificSmallLinearMapEquiv N P g).comp
        (gaussianOmnificSmallLinearMapEquiv M N f) := rfl

/-- Gaussian restriction preserves and reflects exact sequences of small modules. -/
theorem gaussianOmnificSmallLinearMapEquiv_exact_iff (M : Type v) (N : Type w) (P : Type t)
    [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
    [Module GaussianOmnificInteger.{u} M] [Module GaussianOmnificInteger.{u} N]
    [Module GaussianOmnificInteger.{u} P] [Small.{u} M] [Small.{u} N] [Small.{u} P]
    (f : M →ₗ[GaussianOmnificInteger.{u}] N) (g : N →ₗ[GaussianOmnificInteger.{u}] P) :
    Function.Exact (gaussianOmnificSmallLinearMapEquiv M N f)
      (gaussianOmnificSmallLinearMapEquiv N P g) ↔ Function.Exact f g := Iff.rfl

end
end Surreal.Surcomplex
