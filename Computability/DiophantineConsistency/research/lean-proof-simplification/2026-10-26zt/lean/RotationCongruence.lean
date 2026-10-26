import DiophantineConsistency.NativeCyclicRotation

namespace DiophantineConsistency.RephaseSimplification

open NativeCyclicRotation

set_option Elab.async false

-- Exact equality only needs the two coordinates actually read by the
-- definition. In particular, c need not consist of bounded digits.
theorem binaryRotation_congr {n v W W' : ℕ}
    (c : ZMod n → ℕ)
    (hphase : W % v = W' % v)
    (hshift : ((W / v : ℕ) : ZMod n) = ((W' / v : ℕ) : ZMod n)) :
    binaryRotation v W c = binaryRotation v W' c := by
  unfold binaryRotation
  rw [hphase, hshift]

theorem whole_field_rotation_congr {n v a b : ℕ}
    (hv : 0 < v) (c : ZMod n → ℕ)
    (hab : (a : ZMod n) = (b : ZMod n)) :
    binaryRotation v (v*a) c = binaryRotation v (v*b) c := by
  apply binaryRotation_congr
  · simp
  · simpa only [Nat.mul_div_cancel_left _ hv] using hab

-- This is the exact numeric proof body needed by the current rephase
-- module after unfolding its displacement. physical_shift_eq supplies
-- hshift in that module, with its existing original assumptions.
theorem current_numeric_kernel {N : ℕ} (c : ZMod (N*2011) → ℕ)
    (s t : ℕ)
    (hshift : ((2011*s : ℕ) : ZMod (N*2011)) =
      ((2011*t : ℕ) : ZMod (N*2011))) :
    binaryRotation 47 (47*(2011*s)) c = binaryRotation 47 (47*(2011*t)) c := by
  simp only [binaryRotation, Nat.mul_mod_right, pow_zero,
    Nat.mul_div_cancel_left _ (by decide : 0 < 47)]
  rw [hshift]

-- Large digits make the Boolean justification invalid. Equal rotations
-- still agree because their control coordinates agree exactly.
example (c : ZMod 5 → ℕ) :
    binaryRotation 3 (3*2) c = binaryRotation 3 (3*7) c := by
  apply whole_field_rotation_congr (by decide)
  decide

example : binaryRotation 3 0 (fun _ : ZMod 5 => 8) ≠
    (fun _ : ZMod 5 => 8) := by decide

#print axioms binaryRotation_congr
#print axioms whole_field_rotation_congr
#print axioms current_numeric_kernel

end DiophantineConsistency.RephaseSimplification
