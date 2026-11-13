import DiophantineConsistency.MFWangTiles942Core
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
namespace CompactHorizontalCore
open DiophantineConsistency DiophantineConsistency.WangTiles942
open DiophantineConsistency.MF.WangTiles942

def HorizontalBounded (t : Tile) : Prop := t.west < 250 ∧ t.east < 250
instance (t : Tile) : Decidable (HorizontalBounded t) := inferInstanceAs (Decidable (t.west < 250 ∧ t.east < 250))

theorem action_target_mem (j : Fin 430) : (action j).2.2 ∈ targets (action j).2.1 := by
  rw [targets_eq_cache]
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  refine ⟨action j, ?_, rfl⟩
  apply List.mem_filter.mpr
  exact ⟨List.mem_ofFn.mpr ⟨j, rfl⟩, by simp⟩

theorem rail_lt_250 {d : Bool} {q : ℕ} (hq : q ∈ targets d) : rail d q < 250 := by
  have hc : (targets d ∩ Finset.range q).card < (targets d).card := by
    apply Finset.card_lt_card
    exact (Finset.ssubset_iff_of_subset Finset.inter_subset_left).2 ⟨q, hq, by simp⟩
  rw [rail_eq_formula]
  cases d
  · rw [target_counts.1] at hc
    simp only [railFormula, Bool.toNat_false, Nat.mul_zero, Nat.sub_zero]
    omega
  · rw [target_counts.2] at hc
    simp only [railFormula, Bool.toNat_true, Nat.mul_one]
    omega

theorem transition_bounded (j : Fin 430) : HorizontalBounded (transitionRow j).2 := by
  have h := rail_lt_250 (action_target_mem j)
  dsimp only [transitionRow, HorizontalBounded]
  cases hd : (action j).2.1 <;>
    simp only [hd, Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
      Nat.one_mul, Nat.zero_mul] at * <;> omega

theorem copies_bounded : ∀ a : Fin 2, ∀ row ∈ copyRows a.val, HorizontalBounded row.2 := by
  decide +kernel

theorem signals_bounded (d : Bool) : ∀ row ∈ signalRows d, HorizontalBounded row.2 := by
  intro row hrow
  obtain ⟨q,hq,hr⟩ := List.mem_flatMap.mp hrow
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
  have hr' := rail_lt_250 (List.mem_toFinset.mpr hq)
  dsimp only [HorizontalBounded]
  cases d <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
      Nat.one_mul, Nat.zero_mul] at * <;> omega

theorem tail_bounded : ∀ row ∈ tailRows, HorizontalBounded row.2 := by decide +kernel

theorem all_rows_bounded : ∀ row ∈ orderedRows, HorizontalBounded row.2 := by
  simp only [orderedRows, List.forall_mem_append]
  exact ⟨⟨⟨⟨by decide +kernel, List.forall_mem_ofFn_iff.mpr transition_bounded⟩,
    ⟨copies_bounded 1, copies_bounded 0⟩⟩,
    ⟨signals_bounded true, signals_bounded false⟩⟩, tail_bounded⟩
#print axioms CompactHorizontalCore.all_rows_bounded
end CompactHorizontalCore
