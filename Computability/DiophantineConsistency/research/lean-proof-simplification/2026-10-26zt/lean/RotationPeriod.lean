import DiophantineConsistency.NativeCyclicRotation

namespace DiophantineConsistency.RephasePeriod

open NativeCyclicRotation

set_option Elab.async false

theorem binaryRotation_congr {n v W W' : ℕ}
    (c : ZMod n → ℕ)
    (hphase : W % v = W' % v)
    (hshift : ((W / v : ℕ) : ZMod n) = ((W' / v : ℕ) : ZMod n)) :
    binaryRotation v W c = binaryRotation v W' c := by
  unfold binaryRotation
  rw [hphase, hshift]

-- This is a parameter normal form, not a claim that the normalized
-- digits equal c. It includes arbitrary partial phases and digit sizes.
theorem binaryRotation_mod {n v : ℕ} (W : ℕ) (c : ZMod n → ℕ) :
    binaryRotation v (W % (v*n)) c = binaryRotation v W c := by
  apply binaryRotation_congr
  · exact Nat.mod_mod_of_dvd W (Nat.dvd_mul_right v n)
  · rw [Nat.mod_mul_right_div_self, ZMod.natCast_mod]

theorem binaryRotation_eq_of_modEq {n v W W' : ℕ} (c : ZMod n → ℕ)
    (hW : W ≡ W' [MOD v*n]) :
    binaryRotation v W c = binaryRotation v W' c := by
  rw [← binaryRotation_mod W c, ← binaryRotation_mod W' c, hW]

theorem binaryRotation_periodic {n v : ℕ} (c : ZMod n → ℕ) :
    Function.Periodic (fun W => binaryRotation v W c) (v*n) := by
  intro W
  apply binaryRotation_eq_of_modEq
  simp only [Nat.ModEq, Nat.add_mod_right]

-- Nonzero partial phase, arbitrary numeric digits, and two full periods.
example (c : ZMod 5 → ℕ) : binaryRotation 3 7 c = binaryRotation 3 37 c := by
  apply binaryRotation_eq_of_modEq
  decide

#print axioms binaryRotation_congr
#print axioms binaryRotation_mod
#print axioms binaryRotation_eq_of_modEq
#print axioms binaryRotation_periodic

end DiophantineConsistency.RephasePeriod
