import Mathlib.Algebra.Order.Ring.Nat
import Lean.Elab.Tactic.Omega

/-!
New proof cores for `CurrentDummySafety2011.nonwrap_of_short`.
The first theorem isolates the two units of integer slack.  The second
allows both summands to occupy the same penultimate radix window.
No project definitions or precompiled project objects are used here.
-/

namespace ProofDelta20261026.Capacity

theorem two_slots {F δ B Q : ℕ} (hF : F < B) (hδ : δ < B)
    (hcapacity : B + B ≤ Q) : F + δ < Q - 1 := by
  omega

theorem same_window {ρ m F δ : ℕ} (hρ : 2 ≤ ρ) (hm : 1 ≤ m)
    (hF : F < ρ ^ (m - 1)) (hδ : δ < ρ ^ (m - 1)) :
    F + δ < ρ ^ m - 1 := by
  have hcapacity := Nat.mul_le_mul_right (ρ ^ (m - 1)) hρ
  have he : ρ * ρ ^ (m - 1) = ρ ^ m := by
    rw [← pow_succ']
    congr 1
    omega
  rw [he] at hcapacity
  exact two_slots hF hδ (by omega)

/-- Same statement as the current private project theorem. -/
theorem nonwrap_of_short {ρ m F δ : ℕ} (hρ : 2 ≤ ρ) (hm : 2 ≤ m)
    (hF : F < ρ ^ (m - 1)) (hδ : δ < ρ ^ (m - 2)) :
    F + δ < ρ ^ m - 1 := by
  exact same_window hρ (by omega) hF
    (hδ.trans_le (Nat.pow_le_pow_right (by omega) (by omega)))

/-- Direct replacement without introducing either public helper. -/
theorem nonwrap_inline {ρ m F δ : ℕ} (hρ : 2 ≤ ρ) (hm : 2 ≤ m)
    (hF : F < ρ ^ (m - 1)) (hδ : δ < ρ ^ (m - 2)) :
    F + δ < ρ ^ m - 1 := by
  have hδ' := hδ.trans_le (Nat.pow_le_pow_right
    (by omega : 1 ≤ ρ) (by omega : m - 2 ≤ m - 1))
  have hcapacity := Nat.mul_le_mul_right (ρ ^ (m - 1)) hρ
  have he : ρ * ρ ^ (m - 1) = ρ ^ m := by
    rw [← pow_succ']; congr 1; omega
  rw [he] at hcapacity
  omega

-- The conclusion is sharp for radix two: maximal summands give Q - 2.
example : (3 : ℕ) + 3 < 2 ^ 3 - 1 := by decide
example : ¬ ((3 : ℕ) + 4 < 2 ^ 3 - 1) := by decide
example : (0 : ℕ) + 0 < 2 ^ 1 - 1 := by decide

#print axioms two_slots
#print axioms same_window
#print axioms nonwrap_of_short
#print axioms nonwrap_inline

end ProofDelta20261026.Capacity
