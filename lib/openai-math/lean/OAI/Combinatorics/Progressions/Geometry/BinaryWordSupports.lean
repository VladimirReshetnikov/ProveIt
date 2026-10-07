/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.Core
import Mathlib.Data.Fintype.Powerset
import OAI.Combinatorics.Progressions.Estimates.BinaryTupleSorting

namespace OAI

section

namespace Erdos3

open scoped BigOperators

def binaryWordSupport {n : ℕ} (v : Fin n → Fin 2) : Finset (Fin n) :=
  Finset.univ.filter (fun i => v i = 1)

def binaryWordSupportEquiv (n : ℕ) : (Fin n → Fin 2) ≃ Finset (Fin n) where
  toFun := binaryWordSupport
  invFun S i := if i ∈ S then 1 else 0
  left_inv v := by
    funext i
    by_cases h : v i = 1
    · simp [binaryWordSupport, h]
    · simpa only [binaryWordSupport, Finset.mem_filter, Finset.mem_univ, true_and,
        ite_eq_right h] using (binary_eq_zero_of_ne_one (v i) h).symm
  right_inv S := by
    ext i
    simp [binaryWordSupport]

theorem binaryWordSupport_card {n : ℕ} (v : Fin n → Fin 2) :
    (binaryWordSupport v).card = ∑ i, (v i).val := by
  rw [binaryWordSupport, Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  by_cases h : v i = 1
  · simp [h]
  · rw [ite_eq_right h, binary_eq_zero_of_ne_one (v i) h]
    rfl

theorem binaryWordSupport_zero (n : ℕ) :
    binaryWordSupport (fun _ : Fin n => 0) = ∅ := by
  ext i
  simp [binaryWordSupport]

theorem binaryWordSupport_one (n : ℕ) :
    binaryWordSupport (fun _ : Fin n => 1) = Finset.univ := by
  ext i
  simp [binaryWordSupport]

end Erdos3

end

end OAI
