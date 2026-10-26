import Mathlib.Computability.RE

/-! A proof-only, non-effective simplification. No enumerator is defined here. -/
namespace ConstantPredicateReview

/-- Every fixed constant predicate is classically computable.  This does not
produce an effective procedure choosing the right constant from a proposition. -/
theorem constant_computablePred (P : Prop) :
    ComputablePred (fun _ : ℕ => P) := by
  classical
  exact (Computable.const (decide P)).computablePred

/-- The extensional r.e. fact is independent of an actual enumeration algorithm. -/
theorem constant_re (P : Prop) : REPred (fun _ : ℕ => P) :=
  (constant_computablePred P).to_re

/-- Replacing a proof of the same existential proposition does not change a
classical choice.  The equality is definitional by proof irrelevance. -/
theorem choose_proof_irrelevant {α : Sort u} {p : α → Prop}
    (h₁ h₂ : ∃ a, p a) : Classical.choose h₁ = Classical.choose h₂ := rfl

/-- In particular, proof-indexed polynomial selectors have this invariance. -/
theorem selector_proof_irrelevant {α : Sort u} {S : Prop}
    (f : S → α) (h₁ h₂ : S) : f h₁ = f h₂ := rfl

/-- The same statement specialized to a representation selected from an r.e.
proof, with an arbitrary existence theorem in place of Jones's theorem. -/
noncomputable def representation {α : Sort u} (P : Prop)
    (Spec : α → Prop)
    (exists_representation : REPred (fun _ : ℕ => P) → ∃ a, Spec a)
    (h : REPred (fun _ : ℕ => P)) : α :=
  Classical.choose (exists_representation h)

theorem representation_unchanged {α : Sort u} (P : Prop)
    (Spec : α → Prop)
    (exists_representation : REPred (fun _ : ℕ => P) → ∃ a, Spec a)
    (h : REPred (fun _ : ℕ => P)) :
    representation P Spec exists_representation h =
      representation P Spec exists_representation (constant_re P) := rfl

#print axioms constant_computablePred
#print axioms constant_re
#print axioms choose_proof_irrelevant
#print axioms selector_proof_irrelevant
#print axioms representation_unchanged

end ConstantPredicateReview
