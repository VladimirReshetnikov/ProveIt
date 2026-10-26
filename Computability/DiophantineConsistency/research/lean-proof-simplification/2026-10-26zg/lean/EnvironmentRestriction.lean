import Mathlib.Logic.Function.Basic
import Mathlib.Data.Fin.Basic

/-!
The exact semantic mechanism proposed for
ObjectPolynomial.sat_noZeroForm_iff. No assumption about standardness,
well-foundedness, arithmetic, or a model of set theory is used here.
-/
namespace EnvironmentRestriction
universe u v w

/-- Quantification over environments can be replaced by quantification over
assignments when the coordinate map is injective. The explicit default also
handles an empty coordinate type without assuming a nonempty assignment. -/
theorem forall_assignments {ι : Type u} {I : Type v} {V : Type w}
    (coordinates : ι → I) (hinj : Function.Injective coordinates)
    (default : V) (P : (ι → V) → Prop) :
    (∀ env : I → V, P (env ∘ coordinates)) ↔ ∀ assignment, P assignment :=
  (hinj.surjective_comp_right' (fun _ => default)).forall.symm

/-- The actual coordinate map in ObjectPolynomial.noZeroForm. -/
theorem fin_val_forall {V : Type u} (n : Nat) (default : V)
    (P : (Fin n → V) → Prop) :
    (∀ env : Nat → V, P (env ∘ Fin.val)) ↔ ∀ assignment, P assignment :=
  forall_assignments Fin.val Fin.val_injective default P

/-- Guarded unsolvability is simply one predicate on a whole assignment. -/
theorem guarded_unsolvability {V : Type u} (n : Nat) (default : V)
    (Natural : V → Prop) (Equation : (Fin n → V) → Prop) :
    (∀ env : Nat → V,
      (∀ i : Fin n, Natural (env i.val)) → ¬ Equation (env ∘ Fin.val)) ↔
    ∀ assignment : Fin n → V,
      (∀ i, Natural (assignment i)) → ¬ Equation assignment :=
  fin_val_forall n default (fun v => (∀ i, Natural (v i)) → ¬ Equation v)

#print axioms forall_assignments
#print axioms fin_val_forall
#print axioms guarded_unsolvability
end EnvironmentRestriction
