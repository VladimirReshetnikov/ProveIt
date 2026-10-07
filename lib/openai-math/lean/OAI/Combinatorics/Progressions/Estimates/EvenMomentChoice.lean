import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

theorem exists_even_moment_above (p : ℝ) (hp : 0 ≤ p) :
    ∃ q : ℕ, 2 ≤ q ∧ Even q ∧ p ≤ (q : ℝ) ∧ (q : ℝ) ≤ p + 2 := by
  refine ⟨2 * (Nat.floor (p / 2) + 1), by omega, even_two_mul _, ?_, ?_⟩
  · have h := Nat.lt_floor_add_one (p / 2)
    push_cast
    linarith
  · have h := Nat.floor_le (by positivity : 0 ≤ p / 2)
    push_cast
    linarith

end Erdos3

end

end OAI
