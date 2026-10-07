import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

namespace OAI

section

namespace Erdos3

theorem exists_filtered_finite_enumeration {α : Type*} {n : ℕ}
    (c : Fin n → α) (P : α → Prop) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : Fin m → α,
      (∀ j, P (d j)) ∧
      (∀ j, ∃ i, c i = d j) ∧
      ∀ x, P x → (∃ i, c i = x) → ∃ j, d j = x := by
  classical
  let I := {i : Fin n // P (c i)}
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, ?_, (fun j => c (e.symm j).val), ?_, ?_, ?_⟩
  · simpa only [Fintype.card_fin] using Fintype.card_subtype_le (fun i : Fin n => P (c i))
  · intro j
    exact (e.symm j).property
  · intro j
    exact ⟨(e.symm j).val, rfl⟩
  · rintro x hx ⟨i, hi⟩
    have hpi : P (c i) := hi ▸ hx
    refine ⟨e ⟨i, hpi⟩, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hi

theorem exists_filtered_finite_enumeration_range {α : Type*} {n : ℕ}
    (c : Fin n → α) (P : α → Prop) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : Fin m → α,
      ∀ x, (∃ j, d j = x) ↔ P x ∧ ∃ i, c i = x := by
  obtain ⟨m, hm, d, hd, hsub, hcover⟩ := exists_filtered_finite_enumeration c P
  refine ⟨m, hm, d, ?_⟩
  intro x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨hd j, hsub j⟩
  · rintro ⟨hx, hi⟩
    exact hcover x hx hi

end Erdos3

end

end OAI
