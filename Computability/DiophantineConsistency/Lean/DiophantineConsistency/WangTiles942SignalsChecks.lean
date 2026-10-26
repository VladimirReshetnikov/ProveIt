import DiophantineConsistency.WangTiles942Signals

/-! Exact direction, target, halt reception, and retained finish checks. -/

namespace DiophantineConsistency.WangTiles942SignalsChecks

open WangTiles942 WangTiles942Language WangTiles942InputLanguage WangTiles942Signals

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

-- Both sides of a matched plain-input edge are zero, for actual table entries.
example (i j : Fin 942) (b c : Fin 2)
    (hi : (tile i).north = b.val) (hj : (tile j).north = c.val)
    (hm : (tile i).east = (tile j).west) :
    (tile i).east = 0 ∧ (tile j).west = 0 := by
  have he := plain_pair_edge_zero (tile_allowed i) (tile_allowed j) b c hi hj hm
  exact ⟨he,hm.symm.trans he⟩

-- Receives facing each other cannot agree on a nonzero signal.
example (p q : ℕ) (hp : p ∈ targets false) (hq : q ∈ targets true)
    (b c : Fin 2) :
    (⟨0,b.val,rail false p,headColor p b.val⟩ : Tile).east ≠
      (⟨rail true q,c.val,0,headColor q c.val⟩ : Tile).west :=
  directional_rails_disjoint hp hq

-- The first blank action moves right and targets renamed state 1.
example {u : Tile} (hu : Allowed u) (hn : u.north = 0)
    (hm : (transitionRow (0 : Fin 430)).2.east = u.west) :
    u = ⟨7,0,0,4⟩ := by
  have h := right_transition_receiver (0 : Fin 430) (by decide +kernel)
    hu (0 : Fin 2) hn hm
  have htarget : (action (0 : Fin 430)).2.2 = 1 := by decide +kernel
  have hrail : rail true 1 = 7 := by decide +kernel
  simpa only [htarget,hrail,headColor,Fin.val_zero] using h

-- Actual action 5 moves left to state 4; matching forces the left receive.
example {t : Tile} (ht : Allowed t) (hn : t.north = 1)
    (hm : t.east = (transitionRow (5 : Fin 430)).2.west) :
    t = ⟨0,1,205,11⟩ := by
  have h := left_transition_receiver (5 : Fin 430) (by decide +kernel)
    ht (1 : Fin 2) hn hm
  have htarget : (action (5 : Fin 430)).2.2 = 4 := by decide +kernel
  have hrail : rail false 4 = 205 := by decide +kernel
  simpa only [htarget,hrail,headColor,Fin.val_one] using h

-- The actual halt-target action 125 still forces a receive with output 433.
example {u : Tile} (hu : Allowed u) (hn : u.north = 1)
    (hm : (transitionRow (125 : Fin 430)).2.east = u.west) :
    u = ⟨204,1,0,433⟩ := by
  have h := right_transition_receiver (125 : Fin 430) (by decide +kernel)
    hu (1 : Fin 2) hn hm
  have htarget : (action (125 : Fin 430)).2.2 = 215 := by decide +kernel
  have hrail : rail true 215 = 204 := by decide +kernel
  simpa only [htarget,hrail,headColor,Fin.val_one] using h

-- A zero-edge plain finish is allowed, so the nonfinish premise is essential.
example (b : Fin 2) : Allowed (⟨0,b.val,0,438⟩ : Tile) ∧
    (⟨0,b.val,0,438⟩ : Tile) ≠ ⟨0,b.val,0,b.val⟩ := by
  constructor
  · simpa only [Fin.val_zero,Nat.mul_zero,zero_add] using Allowed.finish (0 : Fin 2) b
  · intro he
    have hs := congrArg Tile.south he
    have hb := b.isLt
    simp only at hs
    omega

example {t : Tile} (ht : Allowed t) (b : Fin 2) (hn : t.north = b.val)
    (hw : t.west ≤ 4) (he : t.east ≤ 4) (hs : t.south ≠ 438) :
    t = ⟨0,b.val,0,b.val⟩ := by
  exact plain_zero_edges_nonfinish ht b hn
    (plain_west_small_eq_zero ht b hn (by omega))
    (plain_east_small_eq_zero ht b hn (by omega)) hs

#print axioms plain_east_eq_zero_or_left_receive
#print axioms plain_west_eq_zero_or_right_receive
#print axioms plain_east_small_eq_zero
#print axioms plain_west_small_eq_zero
#print axioms plain_pair_edge_zero
#print axioms right_transition_receiver
#print axioms left_transition_receiver
#print axioms plain_zero_edges_iff_pass_or_finish
#print axioms plain_zero_edges_nonfinish

end DiophantineConsistency.WangTiles942SignalsChecks
