/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def booleanFeature {α R : Type*} [DecidableEq α] [Zero R] [One R]
    (a : Option α) (t : Finset α) : R :=
  match a with
  | none => 1
  | some i => if i ∈ t then 1 else 0

theorem exists_padded_boolean_labels {α : Type*} [DecidableEq α]
    (s : Finset α) (h : ℕ) (hs : s.card ≤ h) :
    ∃ label : Fin h → Option α, ∀ a, (∃ i, label i = some a) ↔ a ∈ s := by
  classical
  let e : s ≃ Fin s.card := Fintype.equivFinOfCardEq (Fintype.card_coe s)
  let label : Fin h → Option α := fun i =>
    if hi : i.val < s.card then some (e.symm ⟨i.val, hi⟩).val else none
  refine ⟨label, ?_⟩
  intro a
  constructor
  · rintro ⟨i, hi⟩
    dsimp [label] at hi
    split_ifs at hi with hc
    · have ha := Option.some.inj hi
      exact ha ▸ (e.symm ⟨i.val, hc⟩).property
  · intro ha
    let j := e ⟨a, ha⟩
    let i : Fin h := ⟨j.val, lt_of_lt_of_le j.isLt hs⟩
    refine ⟨i, ?_⟩
    dsimp [label, i]
    rw [ite_eq_left j.isLt]
    change some (e.symm (e ⟨a, ha⟩)).val = some a
    simp

theorem booleanFeature_product {α ι R : Type*} [DecidableEq α] [Fintype ι] [CommMonoidWithZero R]
    (label : ι → Option α) (s : Finset α)
    (hlabel : ∀ a, (∃ i, label i = some a) ↔ a ∈ s) (t : Finset α) :
    (∏ i, (booleanFeature (label i) t : R)) = if s ⊆ t then 1 else 0 := by
  classical
  by_cases hst : s ⊆ t
  · rw [ite_eq_left hst]
    apply Finset.prod_eq_one
    intro i _
    cases hi : label i with
    | none => rfl
    | some a =>
      have ha := hst ((hlabel a).mp ⟨i, hi⟩)
      simp only [booleanFeature, ha, ite_true]
  · rw [ite_eq_right hst]
    obtain ⟨a, has, hat⟩ := Finset.not_subset.mp hst
    obtain ⟨i, hi⟩ := (hlabel a).mpr has
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp only [hi, booleanFeature, hat, ite_false]

end Erdos3

end

end OAI
