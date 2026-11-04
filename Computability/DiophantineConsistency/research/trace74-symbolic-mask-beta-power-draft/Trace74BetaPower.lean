import DiophantineConsistency.CompactFixedBeta
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74BetaPower
open CompactFixedBeta

/-- The retained fixed beta plus one is its symbolic base power. -/
theorem beta_plus_one : betaNat + 1 = (2^67)^8807 := by
  unfold betaNat
  rw [Nat.sub_add_cancel (Nat.one_le_two_pow (n := 67*8807)), ← pow_mul]

#print axioms Trace74BetaPower.beta_plus_one
end Trace74BetaPower
