import Mathlib.LinearAlgebra.Isomorphisms

namespace OAI

section

namespace Erdos3

variable {K A B C : Type*} [Field K] [AddCommGroup A] [Module K A]
  [AddCommGroup B] [Module K B] [AddCommGroup C] [Module K C]

noncomputable def commonKernelRangeEquiv (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (h : LinearMap.ker f = LinearMap.ker g) : LinearMap.range f ≃ₗ[K] LinearMap.range g :=
  f.quotKerEquivRange.symm.trans ((Submodule.quotEquivOfEq _ _ h).trans g.quotKerEquivRange)

theorem commonKernelRangeEquiv_apply (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (h : LinearMap.ker f = LinearMap.ker g) (x : A) :
    (commonKernelRangeEquiv f g h ⟨f x, ⟨x, rfl⟩⟩ : C) = g x := by
  dsimp only [commonKernelRangeEquiv, LinearEquiv.trans_apply]
  rw [f.quotKerEquivRange_symm_apply_image x ⟨x, rfl⟩]
  rfl

noncomputable def commonKernelSubmoduleEquiv (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (U : Submodule K B) (V : Submodule K C)
    (h : LinearMap.ker f = LinearMap.ker g)
    (hf : LinearMap.range f = U) (hg : LinearMap.range g = V) : U ≃ₗ[K] V :=
  (LinearEquiv.ofEq U (LinearMap.range f) hf.symm).trans
    ((commonKernelRangeEquiv f g h).trans (LinearEquiv.ofEq (LinearMap.range g) V hg))

theorem commonKernelSubmoduleEquiv_apply (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (U : Submodule K B) (V : Submodule K C)
    (h : LinearMap.ker f = LinearMap.ker g)
    (hf : LinearMap.range f = U) (hg : LinearMap.range g = V)
    (x : A) (hx : f x ∈ U) :
    (commonKernelSubmoduleEquiv f g U V h hf hg ⟨f x, hx⟩ : C) = g x :=
  commonKernelRangeEquiv_apply f g h x

theorem commonKernelSubmoduleEquiv_symm_apply (f : A →ₗ[K] B) (g : A →ₗ[K] C)
    (U : Submodule K B) (V : Submodule K C)
    (h : LinearMap.ker f = LinearMap.ker g)
    (hf : LinearMap.range f = U) (hg : LinearMap.range g = V)
    (x : A) (y : V) (hy : g x = y.val) :
    f x = ((commonKernelSubmoduleEquiv f g U V h hf hg).symm y : B) := by
  have hx : f x ∈ U := hf.le ⟨x, rfl⟩
  have he : commonKernelSubmoduleEquiv f g U V h hf hg ⟨f x, hx⟩ = y :=
    Subtype.ext ((commonKernelSubmoduleEquiv_apply f g U V h hf hg x hx).trans hy)
  have hi := congrArg (commonKernelSubmoduleEquiv f g U V h hf hg).symm he
  rw [LinearEquiv.symm_apply_apply] at hi
  exact congrArg Subtype.val hi

end Erdos3

end

end OAI
