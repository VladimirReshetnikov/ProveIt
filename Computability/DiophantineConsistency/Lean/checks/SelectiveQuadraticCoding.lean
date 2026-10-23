import DiophantineConsistency.SelectiveQuadraticCoding
import Mathlib.Data.Fin.VecNotation

open DiophantineConsistency
open SidonPositions (PairIndex)
open SelectiveQuadraticCoding

private def weights : Fin 3 → ℕ := ![0, 1, 2]
private def p01 : PairIndex 2 := ⟨(0, 1), by decide⟩
private def p12 : PairIndex 2 := ⟨(1, 2), by decide⟩
private def supports : Fin 2 → Finset (PairIndex 2) := ![{p01}, {p12}]
private def targets : Fin 2 → ℕ := ![1, 6]

/-- An unused diagonal collides with a different unused pair. -/
example : weights 0 + weights 2 = weights 1 + weights 1 := rfl

private theorem bound : ∀ k p, p ∈ supports k → pairWeight weights p ≤ targets k := by
  unfold supports targets pairWeight weights p01 p12
  decide

private theorem isolation : ∀ k p, p ∈ supports k → Isolated weights p := by
  unfold supports Isolated pairWeight weights p01 p12
  decide

private theorem cross : ∀ k l : Fin 2, k ≠ l → ∀ p ∈ supports k,
    ∀ i j, weights i + weights j + (targets k - pairWeight weights p) ≠ targets l := by
  unfold supports targets pairWeight weights p01 p12
  decide

/-- The row products overlap at positions 3 and 4; the selected targets are safe. -/
example (u : Fin 3 → ℤ) :
    (encoded weights u ^ 2 * combined weights supports (fun _ _ => (1 : ℤ)) targets).coeff 1 =
      2 * u 0 * u 1 := by
  simpa [targets, rowValue, supports, p01, mul_assoc] using
    coeff_square_mul_combined weights supports (fun _ _ => (1 : ℤ)) u targets
      bound isolation cross 0

example (u : Fin 3 → ℤ) :
    (encoded weights u ^ 2 * combined weights supports (fun _ _ => (1 : ℤ)) targets).coeff 6 =
      2 * u 1 * u 2 := by
  simpa [targets, rowValue, supports, p12, mul_assoc] using
    coeff_square_mul_combined weights supports (fun _ _ => (1 : ℤ)) u targets
      bound isolation cross 1

#print axioms coeff_encoded_square
#print axioms coeff_square_mul_combined
