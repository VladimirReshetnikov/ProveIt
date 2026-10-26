import DiophantineConsistency.CurrentCopyParity2011

/-! Focused checks distinguish absolute cyclic positions from cell residues,
retain arbitrary whole-field shifts, and test the exact end of the nine
South-copy fields. No tile-label or native-calibration premise is used. -/

namespace DiophantineConsistency.CurrentCopyParity2011Checks

open CurrentCopyParity2011 CurrentMasks2011 NativeBooleanRotation NativeCyclicRotation

set_option Elab.async false

variable {N : ℕ} [NeZero (N * 2011)]

example (b : ZMod (N * 2011)) (hb : b.val % 2011 = 0) :
    CurrentHighDigits2011.maskDigits (b + 960) = 1 ∧
    CurrentHighDigits2011.maskDigits (b + 968) = 1 := by
  exact ⟨south_mask b hb 0, south_mask b hb 8⟩

-- With two cells, the vanished sources are in the other cell, not at
-- their displayed residues1967 and951 in the origin cell.
example : ((960 : ZMod (2 * 2011)) - 1004).val = 3978 ∧
    ((960 : ZMod (2 * 2011)) - 1004).val % 2011 = 1967 ∧
    ((960 : ZMod (2 * 2011)) - 2020).val = 2962 ∧
    ((960 : ZMod (2 * 2011)) - 2020).val % 2011 = 951 := by decide +kernel

example : ((968 : ZMod (2 * 2011)) - 1004).val % 2011 = 1975 ∧
    ((968 : ZMod (2 * 2011)) - 2020).val % 2011 = 959 := by decide +kernel

-- The next field is deliberately outside the theorem: its spatial source
-- is allowed and its high mask is0, so the nine-field range is substantive.
example : ((969 : ZMod (2 * 2011)) - 2020).val % 2011 = 960 ∧
    CurrentHighDigits2011.maskDigits (969 : ZMod (2 * 2011)) = 0 := by
  constructor
  · decide +kernel
  · rw [CurrentHighDigits2011.maskDigits_nonzero _ (by decide),
      show (969 : ZMod (2 * 2011)).val % 2011 = 969 from by decide]
    exact CurrentHighDigits2011.cellDigit_gaps (by omega)

example : 960 ∈ lowSupport := by
  simp only [lowSupport_def, Finset.mem_union, Finset.mem_range,
    Finset.mem_Ico, Finset.mem_singleton]
  omega

-- Fractional phase0 is compatible with a nonzero whole-field offset19;
-- the rotation in the endpoint really reads physical selector941 here.
example (c : ZMod (N * 2011) → ℕ) (hc : ∀ k, c k ≤ 1) :
    binaryRotation 47 (47 * 19) c 960 = c 941 := by
  rw [rotation_zero_phase (by decide : 0 < 47) (47 * 19) c hc (by decide)]
  norm_num

-- Both Boolean possibilities are retained; Booleanity is essential for
-- deriving equality from even sum, as the pair0,2 illustrates.
example : (0 + 0 : ℕ) % 2 = 0 ∧ (1 + 1 : ℕ) % 2 = 0 ∧
    (0 + 2 : ℕ) % 2 = 0 ∧ (0 : ℕ) ≠ 2 := by decide

#print axioms south_target_residue
#print axioms south_unused_residues
#print axioms south_convolution
#print axioms south_mask
#print axioms south_digit_even
#print axioms south_digit_parity
#print axioms south_copy_eq
#print axioms marker_copy_eq
#print axioms copy_marker_equalities

end DiophantineConsistency.CurrentCopyParity2011Checks
