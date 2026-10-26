import Lean.Elab.Tactic.Omega

/-!
A general arithmetic replacement for the half-radix case splits in
DiophantineConsistency.NativeCyclicRotation (pinned 60e9c5d620c6).
This standalone file uses Lean core; the bridge to the repository's
`shiftDigits` is definitional after a = c k and b = c (k - 1).
-/

namespace ProofSimplification.HalfRadix

def step (s a b : Nat) : Nat := (s * a) % (2 * s) + (s * b) / (2 * s)

theorem step_eq (s a b : Nat) (hs : 0 < s) :
    step s a b = s * (a % 2) + b / 2 := by
  unfold step
  rw [Nat.mul_comm 2 s, Nat.mul_mod_mul_left, Nat.mul_div_mul_left _ _ hs]

/-- The current digit needs no upper bound; only the predecessor does. -/
theorem step_le (s a b : Nat) (hs : 0 < s) (hb : b ≤ 3) :
    step s a b ≤ s + 1 := by
  rw [step_eq s a b hs]
  have hr : a % 2 ≤ 1 := by omega
  have hm := Nat.mul_le_mul_left s hr
  omega

/-- An even half-radix makes the predecessor's high bit the parity bit. -/
theorem step_mod_two (s a b : Nat) (hs : 0 < s)
    (heven : s % 2 = 0) (hb : b ≤ 3) : step s a b % 2 = b / 2 := by
  rw [step_eq s a b hs]
  have hq : b / 2 < 2 := by omega
  have hp : s * (a % 2) % 2 = 0 := by
    rw [Nat.mul_mod, heven, Nat.zero_mul, Nat.zero_mod]
  rw [Nat.add_mod, hp, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hq]

#print axioms step_eq
#print axioms step_le
#print axioms step_mod_two

end ProofSimplification.HalfRadix
