/- Modified for ProveIt: adapt import paths to Mathlib v4.32.0.
Mathematical statements and proofs unchanged. -/
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace OAI

section

namespace Erdos3

theorem scalarKernel_polynomial_envelope {q j N R Q : ℝ}
    (hq : 0 ≤ q) (_hj : 0 ≤ j) (_hN : 0 ≤ N) (hR : 0 ≤ R)
    (hQ : 10 ≤ Q) (hqQ : q + 1 ≤ Q) (hjQ : j ≤ Q) (hNQ : N ≤ Q) (hRQ : R ≤ Q) :
    1 ≤ 16 * Q^3 ∧ q + 1 ≤ 16 * Q^3 ∧ 2 * R + (q + 1) ≤ 16 * Q^3 ∧
    N + q^2 + q ≤ 16 * Q^3 ∧
    j * ((q + 1) * (4 + (q + 1)) + q^2 + 1) ≤ 16 * Q^3 ∧
    j * (q + 1) * (4 + (q + 1) + 2 * R) + R ≤ 16 * Q^3 ∧
    j * ((q + 1) * (4 + (q + 1))) + 3 * N + (q + 1) + q * (8 + (q + 1)) ≤ 16 * Q^3 ∧
    N * (q + 1) ≤ 16 * Q^3 := by
  have hQ0 : 0 ≤ Q := by linarith
  have hqQ' : q ≤ Q := by linarith
  have h4 : (4 : ℝ) ≤ Q := by linarith
  have h8 : (8 : ℝ) ≤ Q := by linarith
  have hQ2 : Q ≤ Q^2 := by nlinarith
  have hQ3 : Q^2 ≤ Q^3 := by nlinarith
  have ha : (q + 1) * (4 + (q + 1)) ≤ 2 * Q^2 := by
    calc
      _ ≤ Q * (Q + Q) := by gcongr
      _ = _ := by ring
  have hu : (q + 1) + q * (8 + (q + 1)) ≤ Q + 2 * Q^2 := by
    calc
      _ ≤ Q + Q * (Q + Q) := by gcongr
      _ = _ := by ring
  have hv : N + q^2 + q ≤ 2 * Q + Q^2 := by
    calc
      _ ≤ Q + Q^2 + Q := by gcongr
      _ = _ := by ring
  have ht : j * ((q + 1) * (4 + (q + 1)) + q^2 + 1) ≤ 4 * Q^3 := by
    calc
      _ ≤ Q * (2 * Q^2 + Q^2 + 1) := by gcongr
      _ ≤ _ := by nlinarith
  have he : j * (q + 1) * (4 + (q + 1) + 2 * R) + R ≤ 4 * Q^3 + Q := by
    calc
      _ ≤ Q * Q * (Q + Q + 2 * Q) + Q := by gcongr
      _ = _ := by ring
  have hc : j * ((q + 1) * (4 + (q + 1))) + 3 * N + (q + 1) + q * (8 + (q + 1)) ≤
      2 * Q^3 + 4 * Q + 2 * Q^2 := by
    calc
      _ = j * ((q + 1) * (4 + (q + 1))) + 3 * N + ((q + 1) + q * (8 + (q + 1))) := by ring
      _ ≤ Q * (2 * Q^2) + 3 * Q + (Q + 2 * Q^2) := by gcongr
      _ = _ := by ring
  have hs : N * (q + 1) ≤ Q^2 := by nlinarith [mul_le_mul hNQ hqQ (by linarith : 0 ≤ q + 1) hQ0]
  exact ⟨by nlinarith, by nlinarith, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by nlinarith, by nlinarith⟩

end Erdos3

end

end OAI
