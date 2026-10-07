import OAI.Combinatorics.Progressions.Linear.RankedCoordinateDecisionTree

namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.with_card_budget {Good : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (B : ℕ) (hB : I.card + d ≤ B) :
    Valid (fun J y => Good J y ∧ J.card ≤ B) I x tree d := by
  induction h with
  | leaf good => exact .leaf ⟨good, by omega⟩
  | @split I x i children d fresh branches ih =>
    apply Valid.split fresh
    intro value
    apply ih value
    rw [Finset.card_insert_of_notMem fresh]
    omega

end Erdos3.CoordinateDecisionTree

end

end OAI
