import DiophantineConsistency.WangTiles942Language

/-! Checks of the actual finite language, including a counterexample to
unrestricted rail injectivity. No tiling, run, or occupancy premise occurs. -/

namespace DiophantineConsistency.WangTiles942LanguageChecks

open WangTiles942 WangTiles942Language

set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

-- The real halt is retained; it occurs at decoder action 125.
example : (action (125 : Fin 430)).2.1 = true ∧
    (action (125 : Fin 430)).2.2 = 215 := by decide +kernel

example : (DecimalMachine215.action 125).2.2 = 215 := by
  have he := congrArg (fun a : Action => a.2.2) (action_eq_decoder (125 : Fin 430))
  exact he.symm.trans (by decide +kernel)

example : 215 ∈ targets true ∧ 215 ∉ targets false := by decide +kernel

example : rail true 215 = 204 ∧ rail false 209 = 249 := by decide +kernel

-- Off the target set, equal rails need not imply equal states.
example : 0 ∉ targets false ∧ 4 ∈ targets false ∧
    rail false 0 = rail false 4 ∧ (0 : ℕ) ≠ 4 := by decide +kernel

-- Both reconstruction directions specialize to the actual finite table.
example : Allowed (tile 1) := tile_allowed 1

example : Allowed (⟨0,2,7,1⟩ : Tile) := by
  rw [← first_transition]
  exact tile_allowed 1

example : ∃ i : Fin 942, tile i = ⟨3,436,4,4⟩ :=
  (allowed_iff_tile _).mp Allowed.initHead

example : Allowed (⟨204,0,0,432⟩ : Tile) := by
  have h : 215 ∈ targets true := by decide +kernel
  have hr : rail true 215 = 204 := by decide +kernel
  have hh := Allowed.receive true 215 h (0 : Fin 2)
  change Allowed (⟨rail true 215,0,0,432⟩ : Tile) at hh
  simpa only [hr] using hh

example {p q : ℕ} (hp : p ∈ targets true) (hq : q ∈ targets true)
    (he : rail true p = rail true q) : p = q :=
  rail_injective_on true hp hq he

example {p q : ℕ} (hp : p ∈ targets false) (hq : q ∈ targets true) :
    rail false p ≠ rail true q := directional_rails_disjoint hp hq

example (i : Fin 942) : 5 < 255 - (tile i).west ∧ 5 < 255 - (tile i).east := by
  obtain ⟨hw,he⟩ := tile_horizontal_bound i
  omega

#print axioms action_target_mem
#print axioms decoded_action_target_mem
#print axioms mem_targets_iff_decoded
#print axioms rail_strict_mono
#print axioms rail_injective_on
#print axioms right_rail_range
#print axioms left_rail_range
#print axioms directional_rails_disjoint
#print axioms allowed_row
#print axioms allowed_iff_tile
#print axioms tile_horizontal_bound
#print axioms complemented_horizontal_positive

end DiophantineConsistency.WangTiles942LanguageChecks
