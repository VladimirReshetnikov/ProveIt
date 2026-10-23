import DiophantineConsistency.NativePellStepDown

open DiophantineConsistency.NativePellStepDown

-- Signed quotient restoration includes negative f, o and rank values.
example : (4 : ℤ) ∣ 1 + 3 * (-3) := by
  exact quotient_dvd (by norm_num) (by norm_num)

example {c f o J T : ℤ} (hT : c * T = o + J * f) :
    c * (T * f - 1) - J * f ^ 2 = o * f - c :=
  quotient_identity hT

-- The sum-residue alternative cannot be dropped without range control.
example : (15 : ℤ) ∣ 12 + 3 ∧ (3 : ℕ) ≠ 12 := by decide

#print axioms index_residues
#print axioms signed_index_residues
#print axioms eq_of_residues
#print axioms source_index
#print axioms source_index_of_strong
#print axioms quotient_dvd
#print axioms quotient_identity
