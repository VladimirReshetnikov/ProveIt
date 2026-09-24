import Mathlib.ModelTheory.Definability

/-!
# Definability is invariant under automorphisms fixing the parameters

The first-order step in `odg:def:thm:norealaxis`, using Mathlib's native
parameter-set definability and semantics for arbitrary formulas.
-/

namespace Surreal.DefinabilityAutomorphisms
open FirstOrder FirstOrder.Language

variable {L : Language} {M : Type*} [L.Structure M] {A : Set M}

/-- Every definable tuple set is invariant under every automorphism fixing all its parameters. -/
theorem invariant {α : Type*} {S : Set (α → M)} (hS : A.Definable L S)
    (e : M ≃[L] M) (hA : ∀ a ∈ A, e a = a) (x : α → M) : (e ∘ x) ∈ S ↔ x ∈ S := by
  obtain ⟨φ, rfl⟩ := Set.definable_iff_exists_formula_sum.mp hS
  change φ.Realize (Sum.elim (Subtype.val : A → M) (e ∘ x)) ↔ φ.Realize (Sum.elim (Subtype.val : A → M) x)
  have he : Sum.elim (Subtype.val : A → M) (e ∘ x) = e ∘ Sum.elim (Subtype.val : A → M) x := by
    funext a
    cases a with
    | inl a => exact (hA a.val a.property).symm
    | inr a => rfl
  rw [he]
  exact StrongHomClass.realize_formula e φ

/-- A moved point disproves unary definability over the fixed parameter set. -/
theorem not_definable₁ {S : Set M} (e : M ≃[L] M) (hA : ∀ a ∈ A, e a = a)
    {x : M} (hx : x ∈ S) (hex : e x ∉ S) : ¬ A.Definable₁ L S := by
  intro hS
  exact hex ((invariant hS e hA (fun _ : Fin 1 => x)).mpr hx)

/-- A definable graph must commute with parameter-fixing automorphisms. -/
theorem definable_graph_commutes {f : M → M}
    (hf : A.Definable₂ L {p : M × M | p.2 = f p.1})
    (e : M ≃[L] M) (hA : ∀ a ∈ A, e a = a) (x : M) : e (f x) = f (e x) := by
  have h := (invariant hf e hA ![x, f x]).mpr
    (show (![x, f x] 0, ![x, f x] 1) ∈ {p : M × M | p.2 = f p.1} from rfl)
  exact h

/-- Failure to commute disproves definability of the graph, allowing all named parameters. -/
theorem not_definable₂_graph {f : M → M} (e : M ≃[L] M) (hA : ∀ a ∈ A, e a = a)
    {x : M} (hx : e (f x) ≠ f (e x)) : ¬ A.Definable₂ L {p : M × M | p.2 = f p.1} :=
  fun hf => hx (definable_graph_commutes hf e hA x)

end Surreal.DefinabilityAutomorphisms
