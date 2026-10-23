import DiophantineConsistency.SelectiveQuadraticCoding
import Mathlib.Data.Fin.VecNotation

/-!
# The package-46 selective weight certificate

Literal weights and its 62 active padded pairs, copied from the delivered
certificate at commit 6d375f2d2d. Kernel reduction checks isolation against
all ordered pairs of 32 coordinates. The certificate alone does not identify
these pairs with the native compiler's support or prove the carry reduction.
-/

namespace DiophantineConsistency.SelectiveCertificate46

open SidonPositions SelectiveQuadraticCoding

set_option maxRecDepth 16000
set_option maxHeartbeats 8000000

def weights : Fin 32 → ℕ := ![0, 175, 169, 108, 60, 123, 81, 158, 139, 78, 63, 166, 164, 37, 12, 130, 40, 174, 50, 21, 56, 14, 59, 76, 101, 150, 143, 15, 149, 57, 146, 147]

def activePair : Fin 62 → PairIndex 31 :=
  ![⟨(0, 0), by decide⟩,
    ⟨(0, 1), by decide⟩,
    ⟨(0, 2), by decide⟩,
    ⟨(0, 3), by decide⟩,
    ⟨(0, 11), by decide⟩,
    ⟨(0, 13), by decide⟩,
    ⟨(0, 14), by decide⟩,
    ⟨(0, 16), by decide⟩,
    ⟨(0, 17), by decide⟩,
    ⟨(0, 18), by decide⟩,
    ⟨(0, 19), by decide⟩,
    ⟨(0, 20), by decide⟩,
    ⟨(0, 21), by decide⟩,
    ⟨(0, 22), by decide⟩,
    ⟨(0, 23), by decide⟩,
    ⟨(0, 24), by decide⟩,
    ⟨(0, 25), by decide⟩,
    ⟨(0, 26), by decide⟩,
    ⟨(0, 27), by decide⟩,
    ⟨(0, 28), by decide⟩,
    ⟨(0, 29), by decide⟩,
    ⟨(0, 30), by decide⟩,
    ⟨(0, 31), by decide⟩,
    ⟨(1, 1), by decide⟩,
    ⟨(1, 2), by decide⟩,
    ⟨(1, 4), by decide⟩,
    ⟨(1, 11), by decide⟩,
    ⟨(1, 17), by decide⟩,
    ⟨(1, 25), by decide⟩,
    ⟨(2, 11), by decide⟩,
    ⟨(2, 17), by decide⟩,
    ⟨(2, 25), by decide⟩,
    ⟨(3, 11), by decide⟩,
    ⟨(3, 25), by decide⟩,
    ⟨(5, 5), by decide⟩,
    ⟨(5, 8), by decide⟩,
    ⟨(6, 18), by decide⟩,
    ⟨(7, 24), by decide⟩,
    ⟨(9, 20), by decide⟩,
    ⟨(10, 17), by decide⟩,
    ⟨(12, 12), by decide⟩,
    ⟨(13, 18), by decide⟩,
    ⟨(13, 19), by decide⟩,
    ⟨(13, 21), by decide⟩,
    ⟨(14, 18), by decide⟩,
    ⟨(14, 19), by decide⟩,
    ⟨(14, 21), by decide⟩,
    ⟨(15, 15), by decide⟩,
    ⟨(16, 21), by decide⟩,
    ⟨(18, 20), by decide⟩,
    ⟨(18, 22), by decide⟩,
    ⟨(19, 19), by decide⟩,
    ⟨(20, 20), by decide⟩,
    ⟨(20, 21), by decide⟩,
    ⟨(21, 21), by decide⟩,
    ⟨(21, 22), by decide⟩,
    ⟨(23, 23), by decide⟩,
    ⟨(24, 31), by decide⟩,
    ⟨(26, 31), by decide⟩,
    ⟨(27, 27), by decide⟩,
    ⟨(28, 30), by decide⟩,
    ⟨(29, 29), by decide⟩]

theorem active_isolated : ∀ k, Isolated weights (activePair k) := by
  unfold Isolated
  decide

theorem maximum_weight : ∀ i, weights i ≤ 175 := by decide

theorem attained_maximum : weights 1 = 175 := rfl

/-- These weights deliberately allow collisions away from the active support. -/
theorem unused_collision : weights 1 + weights 29 = weights 2 + weights 10 := rfl

#print axioms active_isolated

end DiophantineConsistency.SelectiveCertificate46
