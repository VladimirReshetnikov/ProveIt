/-!
The purely logical transport law requires no Mathlib or project imports.
This is a reusable kernel-level lemma; it does not by itself verify that the
separate project-dependent AssignmentTransport.lean file elaborates.
-/

universe u v w z r

namespace ProofRefactoringCore

theorem sumElim_comp_sumMap
    {α : Type u} {β : Type v} {γ : Type w} {δ : Type z} {ρ : Type r}
    (a : γ → ρ) (b : δ → ρ) (f : α → γ) (g : β → δ) :
    (Sum.elim a b) ∘ Sum.map f g = Sum.elim (a ∘ f) (b ∘ g) := by
  funext i
  cases i <;> rfl

#print axioms sumElim_comp_sumMap

end ProofRefactoringCore
