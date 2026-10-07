import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3

theorem approx_section_cutoff {a j r q : ℕ} (haj : a ≤ j) (hjr : j ≤ r) :
    (r - j) * (q + 1) ≤ r * (q + 1) - a := by
  apply Nat.le_sub_of_add_le
  have hmul : a ≤ j * (q + 1) := by nlinarith
  calc
    (r - j) * (q + 1) + a ≤ (r - j) * (q + 1) + j * (q + 1) := Nat.add_le_add_left hmul _
    _ = r * (q + 1) := by rw [← Nat.add_mul, Nat.sub_add_cancel hjr]

theorem approx_moment_cutoff {k r q : ℕ} (hkr : k ≤ r) : q * k ≤ r * (q + 1) := by
  have h := Nat.mul_le_mul_left q hkr
  nlinarith

end Erdos3

end

end OAI
