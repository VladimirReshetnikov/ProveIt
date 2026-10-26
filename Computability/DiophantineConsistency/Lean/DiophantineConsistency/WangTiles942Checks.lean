import DiophantineConsistency.WangTiles942

/-!
# Checks of the exact printed tile table

These checks distinguish abstract table positions from sorted physical
positions, and use the actual first target in discovery-order state names.
No finite tiling is asserted to be a machine computation by this file.
-/

namespace DiophantineConsistency.WangTiles942Checks

open WangTiles942

set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
set_option exponentiation.threshold 1024

example : (targets false).card = 45 ∧ (targets true).card = 199 := by
  decide +kernel

example : 215 ∈ targets true ∧ 0 ∈ targets true := by decide +kernel

example : rail true 1 = 7 ∧ tile 1 = ⟨0,2,7,1⟩ :=
  ⟨by decide +kernel, first_transition⟩

example : tile 0 = ⟨2,435,3,1⟩ ∧ tile 928 = ⟨3,436,4,4⟩ := by
  exact ⟨start_zero, initializer_928⟩

example : DecimalMachine215.action 0 = (true,true,1) :=
  (action_eq_decoder (0 : Fin 430)).symm.trans actual_first_action

example : (DecimalMachine215.stateEquiv 1).val = 93 := DecimalMachine215.stateEquiv_one

example : selectorWeight start = 34876427265 := by decide +kernel

example : physicalPosition 928 = 504 := initializer_position

#print axioms action_eq_decoder
#print axioms targets_eq_decoded
#print axioms rail_eq_formula
#print axioms rail_eq_decoded
#print axioms transitionRow_eq_decoded
#print axioms row_indices_exact
#print axioms row_indices_nodup
#print axioms row_count
#print axioms ordered_rows_perm
#print axioms tile_bounded
#print axioms start_zero
#print axioms initializer_928
#print axioms first_transition
#print axioms physicalPosition_eq_printed
#print axioms physical_initializer

end DiophantineConsistency.WangTiles942Checks
