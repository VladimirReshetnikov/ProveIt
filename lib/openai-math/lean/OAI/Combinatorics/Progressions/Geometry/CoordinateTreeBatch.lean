import OAI.Combinatorics.Progressions.Linear.RankedCoordinateDecisionTree

namespace OAI

section

namespace Erdos3.CoordinateDecisionTree

universe u v

variable {ι : Type u} [DecidableEq ι] {Value : ι → Type v}

theorem exists_query_batch
    (Good : Finset ι → (∀ i, Value i) → Prop) (batch : Finset ι) (d : ℕ) :
    ∀ (I : Finset ι) (x : ∀ i, Value i), Disjoint I batch →
    (∀ y : ∀ i, Value i, (∀ i ∈ I, y i = x i) →
      ∃ tree : CoordinateDecisionTree ι Value, Valid Good (I ∪ batch) y tree d) →
    ∃ tree : CoordinateDecisionTree ι Value, Valid Good I x tree (batch.card + d) := by
  classical
  induction batch using Finset.induction_on with
  | empty =>
    intro I x hdisjoint continuation
    simpa only [Finset.union_empty, Finset.card_empty, Nat.zero_add] using
      continuation x (fun _ _ => rfl)
  | @insert i batch fresh ih =>
    intro I x hdisjoint continuation
    have hi : i ∉ I := by
      intro hi
      exact Finset.disjoint_left.mp hdisjoint hi (Finset.mem_insert_self _ _)
    have hIB : Disjoint (insert i I) batch := by
      apply Finset.disjoint_left.mpr
      intro j hj hbatch
      rcases Finset.mem_insert.mp hj with rfl | hj
      · exact fresh hbatch
      · exact Finset.disjoint_left.mp hdisjoint hj (Finset.mem_insert_of_mem hbatch)
    have hchildren : ∀ value : Value i, ∃ tree : CoordinateDecisionTree ι Value,
        Valid Good (insert i I) (Function.update x i value) tree (batch.card + d) := by
      intro value
      apply ih (insert i I) (Function.update x i value) hIB
      intro y hy
      have hbase : ∀ j ∈ I, y j = x j := by
        intro j hj
        have hji : j ≠ i := by intro h; subst j; exact hi hj
        have h := hy j (Finset.mem_insert_of_mem hj)
        simpa only [Function.update_of_ne hji] using h
      have hunion : insert i I ∪ batch = I ∪ insert i batch := by ext j; simp only [Finset.mem_union, Finset.mem_insert]; tauto
      simpa only [hunion] using continuation y hbase
    choose children hchildren using hchildren
    have hcard : (insert i batch).card + d = (batch.card + d) + 1 := by
      rw [Finset.card_insert_of_notMem fresh]
      omega
    rw [hcard]
    exact ⟨.split i children, .split hi hchildren⟩

end Erdos3.CoordinateDecisionTree

end

end OAI
