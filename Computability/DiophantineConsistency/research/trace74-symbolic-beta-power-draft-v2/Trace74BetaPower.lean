import DiophantineConsistency.CompactFixedBeta
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74BetaPower
open CompactFixedBeta

/-- Keep the exponent symbolic while proving the cancellation and power law. -/
theorem beta_plus_one_generic (a b : ℕ) : 2^(a*b) - 1 + 1 = (2^a)^b := by
  rw [Nat.sub_add_cancel (Nat.one_le_two_pow (n := a*b)), ← pow_mul]

/-- Specialize to the retained beta without deliberately evaluating the power. -/
theorem beta_plus_one : betaNat + 1 = (2^67)^8807 := by
  exact beta_plus_one_generic 67 8807

#print axioms Trace74BetaPower.beta_plus_one
end Trace74BetaPower
