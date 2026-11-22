import Mathlib.Data.Finset.Basic

/-! Criterion used to compare the transition signatures of two output atoms.
Each term of a finite family is an AND of input colours. The family is their OR.
It suffices to test the finitely many actual terms, as assignments of true bits. -/
namespace FiniteClosure.Quotient
variable {α : Type}

def Fires (F : Finset (Finset α)) (input : Finset α) : Prop :=
  ∃ u ∈ F, u ⊆ input

theorem implication_iff (F G : Finset (Finset α)) :
    (∀ X, Fires F X → Fires G X) ↔ ∀ u ∈ F, Fires G u := by
  constructor
  · intro h u hu
    exact h u ⟨u, hu, Finset.Subset.refl _⟩
  · rintro h X ⟨u, hu, hX⟩
    obtain ⟨v, hv, hsub⟩ := h u hu
    exact ⟨v, hv, hsub.trans hX⟩

theorem same_transition_iff (F G : Finset (Finset α)) :
    (∀ X, Fires F X ↔ Fires G X) ↔
    (∀ u ∈ F, Fires G u) ∧ (∀ u ∈ G, Fires F u) := by
  constructor
  · intro h
    exact ⟨(implication_iff F G).mp (fun X => (h X).mp),
      (implication_iff G F).mp (fun X => (h X).mpr)⟩
  · rintro ⟨fg, gf⟩ X
    exact ⟨(implication_iff F G).mpr fg X, (implication_iff G F).mpr gf X⟩
end FiniteClosure.Quotient
