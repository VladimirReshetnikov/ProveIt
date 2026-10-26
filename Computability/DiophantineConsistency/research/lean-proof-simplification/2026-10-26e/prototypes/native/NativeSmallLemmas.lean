import Mathlib.Tactic

/-! ADD-ONLY PROPOSAL; not compiled in the review environment. -/
namespace SimplificationProposals.NativeSmallLemmas

/-- The equation-based analogue of NativeCyclicCarry.reset_of_bound.
No digit bound or quotient-recurrence premise is needed for this direction. -/
theorem reset_of_equation {radix total digit outgoing : ℕ}
    (hsmall : total < radix) (heq : total = digit + radix * outgoing) :
    outgoing = 0 ∧ digit = total := by
  have hz : outgoing = 0 := by
    by_contra hne
    have hpos : 1 ≤ outgoing := by omega
    have hmul : radix ≤ radix * outgoing := by
      simpa only [mul_one] using Nat.mul_le_mul_left radix hpos
    omega
  refine ⟨hz, ?_⟩
  simpa only [hz, mul_zero, add_zero] using heq.symm

/-- Local low-bit information is independent of the unknown outgoing carry.
Use m=16 for padding or m=2048 for the clause, after proving divisibility. -/
theorem residue_of_equation {radix total digit outgoing m : ℕ}
    (heq : total = digit + radix * outgoing) (hmod : radix % m = 0) :
    total % m = digit % m := by
  rw [heq, Nat.add_mod, Nat.mul_mod, hmod]
  simp

#print axioms reset_of_equation
#print axioms residue_of_equation
end SimplificationProposals.NativeSmallLemmas
