import DiophantineConsistency.CurrentCellTranslation2011

namespace DiophantineConsistency.CurrentCellTranslation2011Checks

open CurrentCellTranslation2011

set_option maxRecDepth 10000

variable {N : ℕ} [NeZero (N * 2011)]

-- The cell type is finite without a separate identification with ZMod N.
example : Fintype (Cell N) := inferInstance

-- Both inverse maps are genuine maps of the aligned subtype.
example (t : ℕ) (b : Cell N) : (theta t).symm (theta t b) = b :=
  (theta t).symm_apply_apply b

example (t : ℕ) (b : Cell N) : theta t ((theta t).symm b) = b :=
  (theta t).apply_symm_apply b

-- The two exceptional offsets use sources in the same translated cell.
example (t j : ℕ) (b : Cell N) (hr : t % 2011 = 19) :
    (b : ZMod (N * 2011)) + ((960 + j : ℕ) : ZMod (N * 2011)) - (t : ZMod (N * 2011)) =
      ((theta t b : Cell N) : ZMod (N * 2011)) + ((941 + j : ℕ) : ZMod (N * 2011)) := by
  have h := source_eq_of_remainder_le b t (960 + j) (by omega)
  have he : 960 + j - t % 2011 = 941 + j := by omega
  simpa only [he] using h

example (t j : ℕ) (b : Cell N) (hr : t % 2011 = 20) :
    (b : ZMod (N * 2011)) + ((960 + j : ℕ) : ZMod (N * 2011)) - (t : ZMod (N * 2011)) =
      ((theta t b : Cell N) : ZMod (N * 2011)) + ((940 + j : ℕ) : ZMod (N * 2011)) := by
  have h := source_eq_of_remainder_le b t (960 + j) (by omega)
  have he : 960 + j - t % 2011 = 940 + j := by omega
  simpa only [he] using h

-- Wrapped offsets produce the high residue, never a truncated natural zero.
example (t : ℕ) (b : Cell N) (hr : t % 2011 = 1000) :
    ((b : ZMod (N * 2011)) + 960 - (t : ZMod (N * 2011))).val % 2011 = 1971 := by
  have h := source_residue_of_lt_remainder b t 960 (by omega)
  norm_num only [hr, Nat.cast_ofNat] at h
  exact h

-- Arbitrarily many complete cyclic lengths are explicitly covered.
example (t m : ℕ) (b : Cell N) :
    theta (t + (N * 2011) * m) b = theta t b := by
  rw [theta_add_full_period]

-- A one-cell cyclic word has the same equivalence, which reduces to identity.
example (t : ℕ) (b : Cell 1) : theta t b = b := theta_one t b

#print axioms wholeShift_dvd
#print axioms theta
#print axioms source_eq_of_remainder_le
#print axioms source_residue_of_lt_remainder
#print axioms source_eq_wrapped
#print axioms theta_add_full_period
#print axioms theta_one

end DiophantineConsistency.CurrentCellTranslation2011Checks
