import DiophantineConsistency.QuadraticCoding

/-!
# Simultaneous coefficient extraction for supplied quadratic forms

The row targets are separated by `2*L+1`, where the cubic `L` bounds every
quadratic Sidon position. A row product is supported in its target's closed
radius-`L` interval. Distinct target intervals are disjoint, so one coordinate
square and one combined complementary polynomial recover every supplied row.
This is a coefficient identity, without a complete Jones or no-carry reduction.
-/

namespace DiophantineConsistency.MultiQuadraticCoding

open Polynomial SidonPositions QuadraticCoding
open scoped BigOperators

variable {R : Type*} [CommRing R] {m r : ℕ}

/-- The literal separation between successive row targets. -/
def stride (m : ℕ) : ℕ := 2 * coefficientPosition m + 1

/-- Zero-based row targets, with enough initial space for complementary exponents. -/
def target (m j : ℕ) : ℕ := coefficientPosition m + j * stride m

theorem coefficientPosition_le_target (m j : ℕ) : coefficientPosition m ≤ target m j := by
  exact Nat.le_add_right _ _

/-- Even the complete row support intervals are disjoint. -/
theorem target_intervals_separated (m : ℕ) {j k : ℕ} (hjk : j < k) :
    target m j + coefficientPosition m < target m k - coefficientPosition m := by
  have h := Nat.mul_le_mul_right (stride m) (Nat.succ_le_of_lt hjk)
  rw [Nat.succ_mul] at h
  dsimp only [target, stride] at *
  omega

/-- Every row product vanishes outside its explicit target interval. -/
theorem coeff_row_eq_zero_of_outside (a : PairIndex m → R)
    (u : Fin (m + 1) → R) (j n : ℕ)
    (hn : n < target m j - coefficientPosition m ∨ target m j + coefficientPosition m < n) :
    (encoded u ^ 2 * complementary a (target m j)).coeff n = 0 := by
  classical
  rw [complementary, Finset.mul_sum]
  simp only [finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro p _
  rw [encoded_square]
  simp only [Finset.sum_mul, finsetSum_coeff, monomial_mul_monomial]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro k _
  rw [coeff_monomial]
  have hp : pairWeight p ≤ coefficientPosition m := pairWeight_le p
  have hi : weight m i + weight m k ≤ coefficientPosition m := weight_sum_le i k
  have ht := coefficientPosition_le_target m j
  have hne : weight m i + weight m k + (target m j - pairWeight p) ≠ n := by
    omega
  exact if_neg hne

/-- Other rows contribute zero at the selected target. -/
theorem coeff_row_at_other_target (a : PairIndex m → R)
    (u : Fin (m + 1) → R) {j k : ℕ} (hjk : j ≠ k) :
    (encoded u ^ 2 * complementary a (target m j)).coeff (target m k) = 0 := by
  apply coeff_row_eq_zero_of_outside
  rcases lt_or_gt_of_ne hjk with h | h
  · right
    have hs := target_intervals_separated m h
    omega
  · left
    have hs := target_intervals_separated m h
    omega

/-- One polynomial containing all supplied row coefficient families. -/
noncomputable def combined (a : Fin r → PairIndex m → R) : R[X] :=
  ∑ j, complementary (a j) (target m j.val)

/-- Every target coefficient recovers exactly its own quadratic output. -/
theorem coeff_square_mul_combined (a : Fin r → PairIndex m → R)
    (u : Fin (m + 1) → R) (j : Fin r) :
    (encoded u ^ 2 * combined a).coeff (target m j.val) = 2 * quadraticValue (a j) u := by
  classical
  rw [combined, Finset.mul_sum, finsetSum_coeff, Finset.sum_eq_single j]
  · exact coeff_square_mul_complementary (a j) u _
      (fun p => (pairWeight_le p).trans (coefficientPosition_le_target m j.val))
  · intro k _ hkj
    apply coeff_row_at_other_target
    intro heq
    exact hkj (Fin.ext heq)
  · intro hj
    exact False.elim (hj (Finset.mem_univ j))

/-- A simple strict upper bound for all target positions in a finite row family. -/
def targetBound (m r : ℕ) : ℕ := r * stride m

theorem target_lt_bound (m : ℕ) (j : Fin r) : target m j.val < targetBound m r := by
  have h := Nat.mul_le_mul_right (stride m) (Nat.succ_le_of_lt j.isLt)
  rw [Nat.succ_mul] at h
  dsimp only [target, targetBound, stride] at *
  omega

/-- The target range grows linearly in the number of rows and cubically in dimension. -/
theorem targetBound_eq (m r : ℕ) :
    targetBound m r = r * (8 * m ^ 3 + 4 * m ^ 2 + 4 * m + 1) := by
  unfold targetBound stride coefficientPosition
  ring

end DiophantineConsistency.MultiQuadraticCoding
