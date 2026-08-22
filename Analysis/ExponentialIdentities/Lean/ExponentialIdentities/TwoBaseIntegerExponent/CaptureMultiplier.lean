import Mathlib.GroupTheory.OrderOfElement

/-!
The finite-group core of cleaned-gap capture.

If `g` is the target ratio modulo a cleaned source gap, this identifies exactly the
positive multipliers whose powered target gap captures the source modulus.  The analytic
divergence of the least multiplier uses an external gcd theorem and remains paper-level.
-/

namespace LeanProofs.TwoBaseIntegerExponent.CaptureMultiplier

variable {G : Type*} [Group G] [Finite G]

/-- Exact divisibility criterion for a powered element in a finite group. -/
theorem capture_multiplier_iff_dvd (g : G) (n k : ℕ) :
    g ^ (k * n) = 1 ↔ orderOf g / Nat.gcd (orderOf g) n ∣ k := by
  calc
    g ^ (k * n) = 1 ↔ (g ^ n) ^ k = 1 := by rw [Nat.mul_comm, pow_mul]
    _ ↔ orderOf (g ^ n) ∣ k := orderOf_dvd_iff_pow_eq_one.symm
    _ ↔ orderOf g / Nat.gcd (orderOf g) n ∣ k := by
      rw [orderOf_pow]

end LeanProofs.TwoBaseIntegerExponent.CaptureMultiplier
