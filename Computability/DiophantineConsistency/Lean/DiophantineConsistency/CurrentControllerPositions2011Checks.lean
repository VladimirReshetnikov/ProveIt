import DiophantineConsistency.CurrentControllerPositions2011

namespace DiophantineConsistency.CurrentControllerPositions2011Checks

open CurrentControllerData2011 CurrentControllerPositions2011
set_option Elab.async false

example (k : ℕ) : Function.Injective (cell k) := cell_injective k
example (k : ℕ) (j : ZMod (auxiliary^k)) : cell k j ≠ 3 := cell_ne_three k j
example (k : ℕ) (j : ZMod (auxiliary^k)) :
    position k j ≤ auxiliary^(k+1)-auxiliary^k-auxiliary+3 := position_max k j

-- The one-point orbit k=0 still embeds at position2, disjoint from3.
example (j : ZMod (auxiliary^0)) : position 0 j = 2 := by
  have h : j.val < 1 := ZMod.val_lt j
  have hz : j.val = 0 := by omega
  unfold position
  rw [hz,Nat.mul_zero,Nat.add_zero]
example : (support 0 ∅ 1).card = 1 := by
  simpa only [Finset.card_empty,Nat.zero_add] using support_card 0 ∅ 1 (by decide)
example : (cyclicSupport 0 ∅ 0).card = 0 := by
  simpa only [Finset.card_empty,Nat.zero_add] using cyclicSupport_card 0 ∅ 0 (by decide)

-- The finite subset preserves cardinality, including optional3.
example (k : ℕ) (s : Finset (ZMod (auxiliary^k))) :
    (cyclicSupport k s 1).card = s.card+1 := cyclicSupport_card k s 1 (by decide)

-- Both actual successors are below N, not just congruent modulo N.
example {rw k : ℕ} (hrw : rw < k) (s : Finset (ZMod (auxiliary^k)))
    (ε : ℕ) (j : ZMod (auxiliary^(k+1))) (hj : j ∈ cyclicSupport k s ε) :
    0 < j.val ∧ j.val+1 < auxiliary^(k+1) ∧ j.val+auxiliary^rw < auxiliary^(k+1) :=
  cyclicSupport_safe hrw s ε j hj

#print axioms position_budget
#print axioms position_max
#print axioms position_next_lt
#print axioms position_stride_lt
#print axioms optional_stride_lt
#print axioms position_injective
#print axioms cell_injective
#print axioms cell_ne_three
#print axioms support_card
#print axioms support_safe
#print axioms support_cast_injective
#print axioms cyclicSupport_card
#print axioms cyclicSupport_safe

end DiophantineConsistency.CurrentControllerPositions2011Checks
