import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

namespace OAI

section

namespace Erdos3

theorem exists_finite_fiber_representatives {α β : Type*} {n : ℕ}
    (f : α → β) (P : α → Prop) (c : Fin n → β)
    (hc : ∀ a, P a → ∃ i, c i = f a) :
    ∃ m : ℕ, m ≤ n ∧ ∃ d : Fin m → α,
      (∀ j, P (d j)) ∧
      ∀ a, P a → ∃ j, f (d j) = f a := by
  classical
  let I := {i : Fin n // ∃ a, P a ∧ f a = c i}
  let choose : I → α := fun i => Classical.choose i.property
  have hchoose (i : I) : P (choose i) ∧ f (choose i) = c i.val :=
    Classical.choose_spec i.property
  let e : I ≃ Fin (Fintype.card I) := Fintype.equivFin I
  refine ⟨Fintype.card I, ?_, fun j => choose (e.symm j), ?_, ?_⟩
  · simpa only [Fintype.card_fin] using
      Fintype.card_subtype_le (fun i : Fin n => ∃ a, P a ∧ f a = c i)
  · intro j
    exact (hchoose _).1
  · intro a ha
    obtain ⟨i, hi⟩ := hc a ha
    let i' : I := ⟨i, a, ha, hi.symm⟩
    refine ⟨e i', ?_⟩
    change f (choose (e.symm (e i'))) = f a
    rw [Equiv.symm_apply_apply]
    exact (hchoose i').2.trans hi

end Erdos3

end

end OAI
