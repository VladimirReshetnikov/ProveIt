import DiophantineConsistency.NativeBooleanRotation

namespace DiophantineConsistency.NativeBooleanRotationChecks

open NativeCyclicRotation NativeBooleanRotation

-- The last fractional phase has no incoming high-bit carry for Boolean digits.
example : binaryRotation 47 46 (fun _ : ZMod 1 => 1) 0 = 2 ^ 46 := by
  exact rotation_origin_anchor (by decide) 46 _ (fun _ => by decide) rfl

example : binaryRotation 47 46 (fun _ : ZMod 1 => 1) 0 % 2 = 0 := by
  exact rotation_even (by decide) 46 _ (fun _ => by decide) (by decide) 0

-- Whole-cell rotation includes the wraparound back to the marked origin.
example : binaryRotation 47 94 (fun k : ZMod 2 => if k = 0 then 1 else 0) 0 = 1 := by
  rw [rotation_zero_phase (by decide) 94 _ (by intro k; split_ifs <;> decide) (by decide)]
  decide

-- Without the Boolean hypothesis the half-radix quotient can change the digit.
example : binaryRotation 47 46 (fun _ : ZMod 1 => 2) 0 = 1 ∧
    2 ^ 46 * (2 : ℕ) ≠ 1 := by
  decide +kernel

#print axioms rotation_eq_scaled
#print axioms rotation_le_half
#print axioms rotation_even
#print axioms rotation_zero_phase
#print axioms rotation_origin_anchor

end DiophantineConsistency.NativeBooleanRotationChecks
