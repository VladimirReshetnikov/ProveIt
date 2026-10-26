import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Nat.Prime.Basic
import Lean.Elab.Tactic.Omega

namespace DiophantineConsistency.NativeBinaryScale

theorem width_dvd_exponent {d u : ℕ} (hd : 0 < d)
    (hdiv : 2 ^ d - 1 ∣ 2 ^ u - 1) : d ∣ u := by
  have hm : 2 ^ (u % d) - 1 = 0 := by
    rw [← Nat.pow_sub_one_mod_pow_sub_one 2 d u]
    exact Nat.mod_eq_zero_of_dvd hdiv
  have hpow : 2 ^ (u % d) = 1 := by
    have : 1 ≤ 2 ^ (u % d) := Nat.one_le_two_pow
    omega
  have hzero : u % d = 0 := by
    exact (Nat.pow_right_injective (by decide : 1 < 2))
      (by simpa using hpow : 2 ^ (u % d) = 2 ^ 0)
  exact Nat.dvd_of_mod_eq_zero hzero

#print axioms width_dvd_exponent

end DiophantineConsistency.NativeBinaryScale
