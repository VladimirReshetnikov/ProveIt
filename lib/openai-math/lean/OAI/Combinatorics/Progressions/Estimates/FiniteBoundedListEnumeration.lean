import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Option
import Mathlib.Data.List.OfFn

namespace OAI

section

namespace Erdos3

theorem exists_boundedList_option_padding {α : Type*} {M : ℕ}
    (c : Fin M → α) (P : α → Prop)
    (hcover : ∀ x, P x → ∃ i, c i = x) :
    ∀ (N : ℕ) (l : List α), l.length ≤ N → (∀ x ∈ l, P x) →
      ∃ v : Fin N → Option (Fin M),
        (List.ofFn v).filterMap (Option.map c) = l := by
  intro N
  induction N with
  | zero =>
      intro l hlen hP
      have hl : l = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
      subst l
      exact ⟨fun i => Fin.elim0 i, by simp⟩
  | succ N ih =>
      intro l hlen hP
      cases l with
      | nil =>
          exact ⟨fun _ => none, by simp [List.ofFn_const]⟩
      | cons x l =>
          obtain ⟨i, hi⟩ := hcover x (hP x (by simp))
          have hlen' : l.length ≤ N := Nat.le_of_succ_le_succ hlen
          obtain ⟨v, hv⟩ := ih l hlen' (fun y hy => hP y (by simp [hy]))
          refine ⟨Fin.cons (some i) v, ?_⟩
          simpa [List.ofFn_succ, hi] using congrArg (List.cons x) hv

end Erdos3

end

section

namespace Erdos3

theorem exists_finite_bounded_list_enumeration {α : Type*} {M : ℕ}
    (c : Fin M → α) (P : α → Prop)
    (hvalid : ∀ i, P (c i)) (hcover : ∀ x, P x → ∃ i, c i = x) (N : ℕ) :
    ∃ n : ℕ, n ≤ (M + 1) ^ N ∧ ∃ candidates : Fin n → List α,
      (∀ j, (candidates j).length ≤ N) ∧
      (∀ j x, x ∈ candidates j → P x) ∧
      ∀ l : List α, l.length ≤ N → (∀ x, x ∈ l → P x) →
        ∃ j, candidates j = l := by
  classical
  let V := Fin N → Option (Fin M)
  let e : V ≃ Fin (Fintype.card V) := Fintype.equivFin V
  let decode : V → List α := fun v => (List.ofFn v).filterMap (Option.map c)
  refine ⟨Fintype.card V, ?_, (fun j => decode (e.symm j)), ?_, ?_, ?_⟩
  · simp [V]
  · intro j
    exact (List.length_filterMap_le _ _).trans (by simp)
  · intro j x hx
    obtain ⟨o, _, ho⟩ := List.mem_filterMap.mp hx
    obtain ⟨i, _, hi⟩ := Option.map_eq_some_iff.mp ho
    exact hi ▸ hvalid i
  · intro l hlen hl
    obtain ⟨v, hv⟩ := exists_boundedList_option_padding c P hcover N l hlen hl
    refine ⟨e v, ?_⟩
    simpa only [Equiv.symm_apply_apply] using hv

end Erdos3

end

end OAI
