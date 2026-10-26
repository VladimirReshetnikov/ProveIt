import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Lean.Elab.Tactic.Omega

namespace DiophantineConsistency.NativeBinaryScale

theorem width_dvd_exponent {d u : ℕ} (hd : 0 < d)
    (hdiv : 2 ^ d - 1 ∣ 2 ^ u - 1) : d ∣ u := by
  have hm := Nat.mod_eq_zero_of_dvd hdiv
  rw [Nat.pow_sub_one_mod_pow_sub_one] at hm
  apply Nat.dvd_of_mod_eq_zero
  by_contra hn
  have hsmall := (Nat.pow_le_one_iff hn).mp (Nat.sub_eq_zero_iff_le.mp hm)
  omega

#print axioms width_dvd_exponent

end DiophantineConsistency.NativeBinaryScale
