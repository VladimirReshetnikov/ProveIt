import DiophantineConsistency.WangTiles942InputLanguage

/-! Checks of exact input indices, the actual halt transition, and all
nondeterministic local plain/halt alternatives that must remain present. -/

namespace DiophantineConsistency.WangTiles942InputLanguageChecks

open WangTiles942 WangTiles942Language WangTiles942InputLanguage

set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

example : inputIndex (0 : Fin 215) (0 : Fin 2) = 0 ∧
    inputIndex (214 : Fin 215) (1 : Fin 2) = 429 := by decide +kernel

example : inputIndex (62 : Fin 215) (1 : Fin 2) = 125 ∧
    (action (inputIndex (62 : Fin 215) (1 : Fin 2))).2.2 = 215 := by decide +kernel

example : (transitionRow (inputIndex (0 : Fin 215) (0 : Fin 2))).2 = ⟨0,2,7,1⟩ := by
  decide +kernel

example (q : Fin 215) (b : Fin 2) :
    (inputIndex q b).val / 2 = q.val ∧ (inputIndex q b).val % 2 = b.val :=
  inputIndex_components q b

example (i : Fin 942) (q : Fin 215) (b : Fin 2)
    (hn : (tile i).north = headColor q.val b.val) :
    tile i = (transitionRow (inputIndex q b)).2 :=
  (north_operating_iff_transition (tile_allowed i) q b).mp hn

-- An operating head input cannot be a finish tile.
example (q : Fin 215) (b : Fin 2) :
    ¬ Allowed (⟨0,headColor q.val b.val,0,438⟩ : Tile) := by
  intro ht
  have he := (north_operating_iff_transition ht q b).mp rfl
  have hs := congrArg Tile.south he
  have hw := Bool.toNat_le (action (inputIndex q b)).1
  dsimp only [transitionRow] at hs
  omega

-- Both halt alternatives are genuine members of the finite table language.
example (b : Fin 2) : Allowed (⟨0,432+b.val,0,432+b.val⟩ : Tile) ∧
    Allowed (⟨0,432+b.val,0,438⟩ : Tile) :=
  ⟨Allowed.pass (1 : Fin 2) b, Allowed.finish (1 : Fin 2) b⟩

-- Plain finish is likewise a genuine alternative, not something this packet excludes.
example (b : Fin 2) : Allowed (⟨0,b.val,0,b.val⟩ : Tile) ∧
    Allowed (⟨0,b.val,0,438⟩ : Tile) := by
  simpa only [Fin.val_zero, Nat.mul_zero, zero_add] using
    And.intro (Allowed.pass (0 : Fin 2) b) (Allowed.finish (0 : Fin 2) b)

example (d : Bool) (q : ℕ) (hq : q ∈ targets d) (b : Fin 2) :
    Allowed (⟨d.toNat*rail d q,b.val,(1-d.toNat)*rail d q,headColor q b.val⟩ : Tile) :=
  Allowed.receive d q hq b

-- Actual halt reception remains a plain-input case with output head 433.
example : Allowed (⟨204,1,0,433⟩ : Tile) := by
  have hq : 215 ∈ targets true := by decide +kernel
  have hr : rail true 215 = 204 := by decide +kernel
  have h := Allowed.receive true 215 hq (1 : Fin 2)
  change Allowed (⟨rail true 215,1,0,433⟩ : Tile) at h
  simpa only [hr] using h

example {t : Tile} (ht : Allowed t) : t.north = 433 ↔
    t = ⟨0,433,0,433⟩ ∨ t = ⟨0,433,0,438⟩ := by
  exact north_halt_iff_pass_or_finish ht (1 : Fin 2)

#print axioms inputIndex_val
#print axioms inputIndex_components
#print axioms transition_north_eq_index
#print axioms operating_head_bounds
#print axioms indexed_transition_input
#print axioms north_operating_iff_transition
#print axioms halt_head_eq
#print axioms north_halt_iff_pass_or_finish
#print axioms north_plain_iff

end DiophantineConsistency.WangTiles942InputLanguageChecks
