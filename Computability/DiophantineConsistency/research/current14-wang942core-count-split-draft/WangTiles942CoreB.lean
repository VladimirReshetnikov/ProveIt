import DiophantineConsistency.WangTiles942CoreA
import DiophantineConsistency.WangTiles942CountsFalse
import DiophantineConsistency.WangTiles942CountsTrue

namespace DiophantineConsistency.WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

def ColorsBounded (t : Tile) : Prop :=
  t.west < 256 ∧ t.east < 256 ∧ t.north < 512 ∧ t.south < 512

instance (t : Tile) : Decidable (ColorsBounded t) := inferInstanceAs
  (Decidable (t.west < 256 ∧ t.east < 256 ∧ t.north < 512 ∧ t.south < 512))

/-- The actual table has the stronger vertical bound needed for its weights. -/
def TightColorsBounded (t : Tile) : Prop :=
  t.west < 256 ∧ t.east < 256 ∧ t.north ≤ 438 ∧ t.south ≤ 438

instance (t : Tile) : Decidable (TightColorsBounded t) := inferInstanceAs
  (Decidable (t.west < 256 ∧ t.east < 256 ∧ t.north ≤ 438 ∧ t.south ≤ 438))

theorem target_counts : (targets false).card = 45 ∧ (targets true).card = 199 := by
  exact ⟨target_counts_false, target_counts_true⟩

theorem target_bounds : ∀ d, ∀ q ∈ targetList d, q < 216 := by
  decide +kernel

theorem rail_lt_256 (d : Bool) (q : ℕ) : rail d q < 256 := by
  have h := Finset.card_le_card (Finset.inter_subset_left (s₁ := targets d) (s₂ := Finset.range q))
  rw [rail_eq_formula]
  cases d
  · rw [target_counts.1] at h
    simp only [railFormula, Bool.toNat_false, Nat.mul_zero, Nat.sub_zero]
    omega
  · rw [target_counts.2] at h
    simp only [railFormula, Bool.toNat_true, Nat.mul_one]
    omega

theorem transition_bounded (j : Fin 430) : TightColorsBounded (transitionRow j).2 := by
  have h₀ := rail_lt_256 false (action j).2.2
  have h₁ := rail_lt_256 true (action j).2.2
  have hw := Bool.toNat_le (action j).1
  have hn : headColor (j.val / 2) (j.val % 2) ≤ 438 := by
    have hj := j.isLt
    unfold headColor
    omega
  dsimp only [transitionRow, TightColorsBounded]
  cases hd : (action j).2.1 <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
      Nat.one_mul, Nat.zero_mul] <;> omega

theorem copies_bounded : ∀ a : Fin 2, ∀ row ∈ copyRows a.val, TightColorsBounded row.2 := by
  decide +kernel

theorem signals_bounded (d : Bool) : ∀ row ∈ signalRows d, TightColorsBounded row.2 := by
  intro row hrow
  obtain ⟨q,hq,hr⟩ := List.mem_flatMap.mp hrow
  obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hr
  have hq' := target_bounds d q hq
  have hb' : b < 2 := List.mem_range.mp hb
  have hr' := rail_lt_256 d q
  dsimp only [TightColorsBounded]
  unfold headColor
  cases d <;>
    simp only [Bool.toNat_false, Bool.toNat_true, Nat.sub_zero, Nat.sub_self,
      Nat.one_mul, Nat.zero_mul] at * <;> omega

theorem tail_bounded : ∀ row ∈ tailRows, TightColorsBounded row.2 := by
  decide +kernel

end DiophantineConsistency.WangTiles942
