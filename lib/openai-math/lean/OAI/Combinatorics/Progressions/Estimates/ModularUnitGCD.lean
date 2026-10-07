import Mathlib.Data.ZMod.Basic

namespace OAI

section

namespace Erdos3

theorem zmod_gcd_unit_mul {N : ℕ} (u : (ZMod N)ˣ) (t : ZMod N) :
    Nat.gcd ((u : ZMod N) * t).val N = Nat.gcd t.val N := by
  rw [ZMod.val_mul, ← Nat.gcd_rec, Nat.gcd_comm]
  exact Nat.Coprime.gcd_mul_left_cancel t.val (ZMod.val_coe_unit_coprime u)

theorem zmod_gcd_mul_unit {N : ℕ} (t : ZMod N) (u : (ZMod N)ˣ) :
    Nat.gcd (t * (u : ZMod N)).val N = Nat.gcd t.val N := by
  rw [mul_comm]
  exact zmod_gcd_unit_mul u t

end Erdos3

end

end OAI
