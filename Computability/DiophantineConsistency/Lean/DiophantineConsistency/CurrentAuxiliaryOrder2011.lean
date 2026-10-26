import DiophantineConsistency.PrimePowerOrder
import DiophantineConsistency.CurrentControllerData2011

/-! The actual auxiliary generator has the exact prime-power order.
Only the previously checked literal lift is used. No full-modulus CRT
orbit, affine coordinate enumeration, or subset realization is asserted. -/
namespace DiophantineConsistency.CurrentAuxiliaryOrder2011

open CurrentControllerData2011
open PrimePowerOrder
set_option Elab.async false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

attribute [local irreducible] CurrentControllerData2011.B

theorem generator_gt_one : 1 < B^(auxiliary-1) := by
  have hm := Nat.mod_le (B^(auxiliary-1)) (auxiliary^2)
  rw [auxiliary_lift] at hm
  omega

theorem generator_mod_prime : B^(auxiliary-1) % auxiliary = 1 := by
  calc
    B^(auxiliary-1) % auxiliary =
        (B^(auxiliary-1) % auxiliary^2) % auxiliary :=
      (Nat.mod_mod_of_dvd _ (dvd_pow_self auxiliary (by decide : 2 ≠ 0))).symm
    _ = 1 := by rw [auxiliary_lift]; decide

/-- Actual p-divisibility, with no supplied principal-unit premise. -/
theorem generator_dvd : auxiliary ∣ B^(auxiliary-1)-1 := by
  apply (Nat.modEq_iff_dvd' generator_gt_one.le).mp
  change 1 % auxiliary = B^(auxiliary-1) % auxiliary
  rw [generator_mod_prime]
  decide

/-- The checked nonzero first lift excludes divisibility by p². -/
theorem generator_not_square : ¬ auxiliary^2 ∣ B^(auxiliary-1)-1 := by
  intro hd
  have he := (Nat.modEq_iff_dvd' generator_gt_one.le).mpr hd
  change 1 % auxiliary^2 = B^(auxiliary-1) % auxiliary^2 at he
  have h1 : 1 % auxiliary^2 = 1 := by decide
  exact lift_ne_one (he.symm.trans h1)

theorem generator_not_dvd : ¬ auxiliary ∣ B^(auxiliary-1) :=
  not_dvd_of_dvd_sub_one prime_auxiliary generator_gt_one.le generator_dvd

theorem generator_exact_lift (k : ℕ) :
    auxiliary^(k+1) ∣ (B^(auxiliary-1))^(auxiliary^k)-1 ∧
      ¬ auxiliary^(k+2) ∣ (B^(auxiliary-1))^(auxiliary^k)-1 :=
  exact_lift prime_auxiliary auxiliary_odd generator_dvd generator_not_square k

theorem generator_order_succ (k : ℕ) :
    orderOf ((B : ZMod (auxiliary^(k+1)))^(auxiliary-1)) = auxiliary^k := by
  simpa only [Nat.cast_pow] using
    order_succ prime_auxiliary auxiliary_odd generator_dvd generator_not_square k

theorem generator_order (n : ℕ) (hn : 1 ≤ n) :
    orderOf ((B : ZMod (auxiliary^n))^(auxiliary-1)) = auxiliary^(n-1) := by
  simpa only [Nat.cast_pow] using
    order_prime_power prime_auxiliary auxiliary_odd generator_dvd generator_not_square hn

end DiophantineConsistency.CurrentAuxiliaryOrder2011
