import Mathlib.Algebra.Exact.Basic
import Mathlib.Algebra.Module.LinearMap.Defs

/-!
# Module structures and morphisms under a split scalar reflection

The algebraic mechanism in `osq:thm:modules`. When scalar actions factor
through a split ring map, restriction and inflation are inverse on native
Module structures over the same additive group. Linear maps retain their
underlying functions, with identity, composition and exactness preserved.
-/

universe u v w t z
namespace Surreal.ModuleReflection
noncomputable section
variable {A : Type u} {D : Type v} [Ring A] [Ring D]

/-- Restriction and inflation identify module structures when every action factors through a retraction. -/
def moduleEquiv (r : A →+* D) (s : D →+* A) (hs : ∀ d, r (s d) = d)
    (M : Type w) [AddCommGroup M]
    (hscalar : ∀ (P : Module A M), letI := P; ∀ (a : A) (m : M), a • m = s (r a) • m) :
    Module A M ≃ Module D M where
  toFun P := by
    letI := P
    exact Module.compHom M s
  invFun Q := by
    letI := Q
    exact Module.compHom M r
  left_inv P := by
    apply Module.ext'
    intro a m
    exact (hscalar P a m).symm
  right_inv Q := by
    letI := Q
    apply Module.ext'
    intro d m
    change r (s d) • m = d • m
    rw [hs]

variable (r : A →+* D) (s : D →+* A)
  {M : Type w} {N : Type t} {P : Type z}
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P]
  [Module A M] [Module A N] [Module A P]

/-- Linear maps are unchanged when both actions factor through the same coefficient retraction. -/
def linearMapEquiv
    (hM : ∀ (a : A) (m : M), a • m = s (r a) • m)
    (hN : ∀ (a : A) (n : N), a • n = s (r a) • n) :
    (M →ₗ[A] N) ≃ (letI := Module.compHom M s; letI := Module.compHom N s; M →ₗ[D] N) := by
  letI := Module.compHom M s
  letI := Module.compHom N s
  exact
    { toFun := fun f => { f.toAddMonoidHom with map_smul' := fun d m => f.map_smul (s d) m }
      invFun := fun g =>
        { g.toAddMonoidHom with
          map_smul' := fun a m => by
            calc
              g (a • m) = g (s (r a) • m) := congrArg g (hM a m)
              _ = s (r a) • g m := g.map_smul (r a) m
              _ = a • g m := (hN a (g m)).symm }
      left_inv := fun f => LinearMap.ext (fun _ => rfl)
      right_inv := fun g => LinearMap.ext (fun _ => rfl) }

/-- Both directions retain the same underlying function. -/
theorem linearMapEquiv_apply
    (hM : ∀ (a : A) (m : M), a • m = s (r a) • m)
    (hN : ∀ (a : A) (n : N), a • n = s (r a) • n) (f : M →ₗ[A] N) (m : M) :
    linearMapEquiv r s hM hN f m = f m := rfl

/-- Identity morphisms are preserved. -/
theorem linearMapEquiv_id (hM : ∀ (a : A) (m : M), a • m = s (r a) • m) :
    linearMapEquiv r s hM hM (LinearMap.id : M →ₗ[A] M) =
      (letI := Module.compHom M s; (LinearMap.id : M →ₗ[D] M)) := rfl

/-- Composition is preserved on the unchanged underlying maps. -/
theorem linearMapEquiv_comp
    (hM : ∀ (a : A) (m : M), a • m = s (r a) • m)
    (hN : ∀ (a : A) (n : N), a • n = s (r a) • n)
    (hP : ∀ (a : A) (p : P), a • p = s (r a) • p)
    (f : M →ₗ[A] N) (g : N →ₗ[A] P) :
    linearMapEquiv r s hM hP (g.comp f) =
      (linearMapEquiv r s hN hP g).comp (linearMapEquiv r s hM hN f) := rfl

/-- Exactness is preserved and reflected because image and kernel are unchanged. -/
theorem linearMapEquiv_exact_iff
    (hM : ∀ (a : A) (m : M), a • m = s (r a) • m)
    (hN : ∀ (a : A) (n : N), a • n = s (r a) • n)
    (hP : ∀ (a : A) (p : P), a • p = s (r a) • p)
    (f : M →ₗ[A] N) (g : N →ₗ[A] P) :
    Function.Exact (linearMapEquiv r s hM hN f) (linearMapEquiv r s hN hP g) ↔
      Function.Exact f g := Iff.rfl

end
end Surreal.ModuleReflection
