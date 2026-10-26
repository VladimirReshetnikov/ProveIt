import Lean.Elab.Tactic.Omega

/-!
Proof kernel for the new CurrentPackingRank2011.rank_gt_twice_window.
The actual packing/source theorem is not imported here. Its exponential
identity and the already-proved lower/cast bounds are explicit hypotheses.
-/

namespace FullExponentGrowth

theorem twice_window_lt_cube (u q : Nat) (hq : q = 2 ^ u) :
    2 * u < q ^ 3 := by
  rw [hq, ← Nat.pow_mul]
  exact Nat.lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := u * 3))

theorem rank_gt_twice_window (u q blocks : Nat) (rank : Int)
    (hq : q = 2 ^ u) (hlower : q ^ 3 ≤ blocks)
    (hcast : Int.ofNat blocks = rank) : Int.ofNat (2 * u) < rank := by
  have hc : 2 * u < q ^ 3 := by
    rw [hq, ← Nat.pow_mul]
    exact Nat.lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n := u * 3))
  have hn := Nat.lt_of_lt_of_le hc hlower
  rw [← hcast]
  exact Int.ofNat_lt.mpr hn

example : 2 * 0 < (2 ^ 0 : Nat) ^ 3 := twice_window_lt_cube 0 1 rfl
example : 2 * 1 < (2 ^ 1 : Nat) ^ 3 := twice_window_lt_cube 1 2 rfl

#print axioms twice_window_lt_cube
#print axioms rank_gt_twice_window

end FullExponentGrowth
