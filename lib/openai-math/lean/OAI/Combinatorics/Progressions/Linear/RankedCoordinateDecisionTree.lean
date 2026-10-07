import OAI.Combinatorics.Progressions.Geometry.CoordinateTreeTrace

namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v w

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem Valid.map {Good Better : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d : ℕ}
    (h : Valid Good I x tree d) (hmap : ∀ J y, Good J y → Better J y) : Valid Better I x tree d := by
  induction h with
  | leaf good => exact .leaf (hmap _ _ good)
  | split fresh branches ih => exact .split fresh ih

theorem Valid.substitute {Good Better : Finset ι → (∀ i, Value i) → Prop}
    {I : Finset ι} {x : ∀ i, Value i} {tree : CoordinateDecisionTree ι Value} {d e : ℕ}
    (h : Valid Good I x tree d)
    (replace : ∀ J y, Good J y → ∃ next : CoordinateDecisionTree ι Value, Valid Better J y next e) :
    ∃ next : CoordinateDecisionTree ι Value, Valid Better I x next (d + e) := by
  classical
  induction h with
  | @leaf I x d good =>
    obtain ⟨next, hnext⟩ := replace I x good
    exact ⟨next, hnext.mono (by omega)⟩
  | @split I x i children d fresh branches ih =>
    choose next hnext using ih
    have hsum : d + 1 + e = (d + e) + 1 := by omega
    rw [hsum]
    exact ⟨.split i next, .split fresh hnext⟩

theorem exists_of_rank_decreasing_step
    (State : Finset ι → (∀ i, Value i) → Type w)
    (rank : ∀ I x, State I x → ℕ) (Good : Finset ι → (∀ i, Value i) → Prop) (cost : ℕ)
    (step : ∀ I x (state : State I x), ∃ tree : CoordinateDecisionTree ι Value,
      Valid (fun J y => Good J y ∨ ∃ next : State J y, rank J y next < rank I x state) I x tree cost)
    (I : Finset ι) (x : ∀ i, Value i) (state : State I x) :
    ∃ tree : CoordinateDecisionTree ι Value, Valid Good I x tree (cost * (rank I x state + 1)) := by
  have build : ∀ n : ℕ, ∀ I x (state : State I x), rank I x state = n →
      ∃ tree : CoordinateDecisionTree ι Value, Valid Good I x tree (cost * (n + 1)) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro I x state hn
      obtain ⟨tree, htree⟩ := step I x state
      have replace : ∀ J y, (Good J y ∨ ∃ next : State J y, rank J y next < rank I x state) →
          ∃ nextTree : CoordinateDecisionTree ι Value, Valid Good J y nextTree (cost * n) := by
        intro J y hleaf
        rcases hleaf with hgood | ⟨next, hlt⟩
        · exact ⟨.leaf, .leaf hgood⟩
        · have hlt' : rank J y next < n := by simpa only [hn] using hlt
          obtain ⟨nextTree, hnext⟩ := ih (rank J y next) hlt' J y next rfl
          exact ⟨nextTree, hnext.mono (Nat.mul_le_mul_left cost (by omega))⟩
      simpa only [Nat.mul_add, Nat.mul_one, Nat.add_comm] using htree.substitute replace
  exact build (rank I x state) I x state rfl

end Erdos3.CoordinateDecisionTree

end

end OAI
