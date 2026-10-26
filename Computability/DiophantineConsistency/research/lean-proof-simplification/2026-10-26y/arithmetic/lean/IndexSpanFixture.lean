import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

namespace DiophantineConsistency.SidonPositions
abbrev PairIndex (m : ℕ) :=
  {p : Fin (m + 1) × Fin (m + 1) // p.1 ≤ p.2}
end DiophantineConsistency.SidonPositions

namespace DiophantineConsistency.SelectiveQuadraticCoding
open SidonPositions
variable {m : ℕ}
def pairWeight (w : Fin (m + 1) → ℕ) (p : PairIndex m) : ℕ :=
  w p.val.1 + w p.val.2
end DiophantineConsistency.SelectiveQuadraticCoding

namespace DiophantineConsistency.SelectiveCertificate52
open SidonPositions
def weights : Fin 32 → ℕ := ![81, 51, 169, 164, 28, 174, 146, 0, 32, 20, 24, 154, 45, 143, 140, 33, 141, 44, 123, 135, 11, 119, 148, 145, 18, 166, 1, 158, 25, 163, 29, 5]

def activePair : Fin 71 → PairIndex 31 :=
  ![⟨(0, 0), by decide⟩,
    ⟨(0, 1), by decide⟩,
    ⟨(0, 2), by decide⟩,
    ⟨(0, 3), by decide⟩,
    ⟨(0, 4), by decide⟩,
    ⟨(0, 5), by decide⟩,
    ⟨(0, 6), by decide⟩,
    ⟨(0, 7), by decide⟩,
    ⟨(0, 8), by decide⟩,
    ⟨(0, 9), by decide⟩,
    ⟨(0, 10), by decide⟩,
    ⟨(0, 11), by decide⟩,
    ⟨(0, 12), by decide⟩,
    ⟨(0, 13), by decide⟩,
    ⟨(0, 14), by decide⟩,
    ⟨(0, 15), by decide⟩,
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
end DiophantineConsistency.SelectiveCertificate52

namespace DiophantineConsistency.NativeQuadraticParent
open SidonPositions
def rowSupportIndices : Fin 22 → Finset (Fin 71) :=
  ![{32, 1, 25, 0},
    {37, 1, 17, 25, 0},
    {35, 1, 11, 22, 0},
    {48, 10, 17, 18, 21, 0},
    {50, 52, 13, 53, 55, 18, 20, 21},
    {50, 14, 58, 19, 20, 0},
    {49, 12, 51, 13, 54, 14, 60, 0},
    {57, 16, 62, 20, 21, 22, 23, 0},
    {63, 21, 31, 0},
    {61, 20, 24},
    {65, 23, 66, 24, 31, 0},
    {45, 6, 47, 9, 13, 14, 18, 20, 27},
    {32, 33, 36, 37, 1, 39, 40, 2, 42, 3, 47, 9, 17, 20, 25, 27, 0},
    {34, 35, 1, 38, 2, 41, 3, 4, 11, 0},
    {43, 5, 26},
    {44, 5, 8, 20, 27, 0},
    {56, 15, 68, 27, 28, 0},
    {46, 7, 24, 29},
    {70, 29, 30},
    {67, 26, 30, 0},
    {56, 15, 69, 28, 30, 0},
    {59, 18, 64, 21, 0}]

/-- The exact support, carried through the certified active-pair map. -/
def rowSupport (k : Fin 22) : Finset (PairIndex 31) :=
  (rowSupportIndices k).image SelectiveCertificate52.activePair
end DiophantineConsistency.NativeQuadraticParent

namespace DiophantineConsistency.NativeQuadraticPositions
open SidonPositions SelectiveQuadraticCoding NativeQuadraticParent
set_option maxRecDepth 16000
def target (k : Fin 22) : ℕ := 349 * (k.val + 1)
private theorem index_span : ∀ k i, i ∈ rowSupportIndices k →
    target k - pairWeight SelectiveCertificate52.weights (SelectiveCertificate52.activePair i) ≤ 7516 := by
  intro k i hi
  by_cases hk : k.val < 21
  · have ht : target k ≤ 7516 := by dsimp [target]; omega
    exact (Nat.sub_le _ _).trans ht
  · have hk21 : k = 21 := Fin.ext (by have := k.isLt; omega)
    subst k
    change i ∈ {59, 18, 64, 21, 0} at hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;> decide

theorem encoding_span (k : Fin 22) (p : PairIndex 31) (hp : p ∈ rowSupport k) :
    target k - pairWeight SelectiveCertificate52.weights p ≤ 7516 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hp
  exact index_span k i hi

#print axioms encoding_span
end DiophantineConsistency.NativeQuadraticPositions
