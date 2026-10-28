import Mathlib.Tactic.Zify
import Mathlib.Tactic.LinearCombination
import Mathlib.Order.Fin.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Explicit cubic-size positions with unique unordered pair sums

For indices `0 ≤ i ≤ m`, use `(2*m^2+1)*i+i^2`. The square-sum remainder is
strictly below the radix, so equality of two pair sums determines both the
index sum and the square sum. Consequently it determines the unordered pair.
These are supplied natural data; this file does not assert a Jones reduction
using them.
-/

namespace DiophantineConsistency.SidonPositions

/-- The low-order square sums fit strictly below this radix. -/
def radix (m : ℕ) : ℕ := 2 * m ^ 2 + 1

/-- Explicit positions for a constant coordinate zero and `m` other coordinates. -/
def weight (m : ℕ) (i : Fin (m + 1)) : ℕ := radix m * i.val + i.val ^ 2

@[simp] theorem radix_pos (m : ℕ) : 0 < radix m := by
  simp [radix]

@[simp] theorem weight_zero (m : ℕ) : weight m 0 = 0 := by
  simp [weight]

private theorem val_le (m : ℕ) (i : Fin (m + 1)) : i.val ≤ m := by
  have := i.isLt
  omega

private theorem square_le (m : ℕ) (i : Fin (m + 1)) : i.val ^ 2 ≤ m ^ 2 := by
  exact Nat.pow_le_pow_left (val_le m i) 2

/-- Separating the quotient and remainder loses no pair information. -/
theorem square_sum_lt_radix (m : ℕ) (i j : Fin (m + 1)) :
    i.val ^ 2 + j.val ^ 2 < radix m := by
  have hi := square_le m i
  have hj := square_le m j
  dsimp [radix]
  omega

/-- Equal position sums have equal index sums and equal square sums. -/
theorem sums_of_weight_sum_eq {m : ℕ} {i j k l : Fin (m + 1)}
    (h : weight m i + weight m j = weight m k + weight m l) :
    i.val + j.val = k.val + l.val ∧
      i.val ^ 2 + j.val ^ 2 = k.val ^ 2 + l.val ^ 2 := by
  have regroup :
      radix m * (i.val + j.val) + (i.val ^ 2 + j.val ^ 2) =
        radix m * (k.val + l.val) + (k.val ^ 2 + l.val ^ 2) := by
    simpa only [weight, Nat.mul_add, add_assoc, add_left_comm, add_comm] using h
  have remainder := congrArg (fun n => n % radix m) regroup
  have hsquares : i.val ^ 2 + j.val ^ 2 = k.val ^ 2 + l.val ^ 2 := by
    simpa only [Nat.add_mod, Nat.mul_mod_right, zero_add,
      Nat.mod_eq_of_lt (square_sum_lt_radix m i j),
      Nat.mod_eq_of_lt (square_sum_lt_radix m k l)] using remainder
  have hproducts : radix m * (i.val + j.val) = radix m * (k.val + l.val) := by
    rw [hsquares] at regroup
    exact Nat.add_right_cancel regroup
  have hsum : i.val + j.val = k.val + l.val :=
    Nat.eq_of_mul_eq_mul_left (radix_pos m) hproducts
  exact ⟨hsum, hsquares⟩

/-- The positions form an explicit B₂ (Sidon) set, allowing repeated indices. -/
theorem weight_sum_eq_iff {m : ℕ} (i j k l : Fin (m + 1)) :
    weight m i + weight m j = weight m k + weight m l ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by
  constructor
  · intro h
    obtain ⟨hsum, hsquares⟩ := sums_of_weight_sum_eq h
    simp only [Fin.ext_iff]
    zify at hsum hsquares ⊢
    have hfactor : 2 * (((i.val : ℤ) - k.val) * ((i.val : ℤ) - l.val)) = 0 := by
      linear_combination hsquares + ((i.val : ℤ) - j.val - k.val - l.val) * hsum
    have hz : ((i.val : ℤ) - k.val) * ((i.val : ℤ) - l.val) = 0 := by omega
    rcases mul_eq_zero.mp hz with h | h
    · left; constructor <;> omega
    · right; constructor <;> omega
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · rfl
    · exact Nat.add_comm _ _

/-- In particular, every supplied index has a distinct position. -/
theorem weight_injective (m : ℕ) : Function.Injective (weight m) := by
  intro i j h
  rcases (weight_sum_eq_iff i i j j).mp (congrArg (fun n => n + n) h) with h | h <;>
    exact h.1

/-- An explicit cubic bound for the largest position. -/
theorem weight_le_cubic (m : ℕ) (i : Fin (m + 1)) :
    weight m i ≤ 2 * m ^ 3 + m ^ 2 + m := by
  calc
    weight m i ≤ radix m * m + m ^ 2 :=
      Nat.add_le_add (Nat.mul_le_mul_left (radix m) (val_le m i)) (square_le m i)
    _ = 2 * m ^ 3 + m ^ 2 + m := by unfold radix; ring

/-- The bound is attained by the final index. -/
@[simp] theorem weight_last (m : ℕ) :
    weight m (Fin.last m) = 2 * m ^ 3 + m ^ 2 + m := by
  simp only [weight, Fin.val_last, radix]
  ring

/-- For positive dimensions the maximum is at most four times the cube. -/
theorem weight_le_four_cube {m : ℕ} (hm : 1 ≤ m) (i : Fin (m + 1)) :
    weight m i ≤ 4 * m ^ 3 := by
  have h1 : m ≤ m * m := by simpa using Nat.mul_le_mul_left m hm
  have h2 : m * m ≤ m * m * m := by simpa using Nat.mul_le_mul_left (m * m) hm
  have h := weight_le_cubic m i
  nlinarith [h1, h2]

/-- A sum of two positions also has a cubic numerical bound. -/
theorem weight_sum_le {m : ℕ} (i j : Fin (m + 1)) :
    weight m i + weight m j ≤ 4 * m ^ 3 + 2 * m ^ 2 + 2 * m := by
  have hi := weight_le_cubic m i
  have hj := weight_le_cubic m j
  omega

/-- Canonical unordered pairs: repeated indices are included. -/
abbrev PairIndex (m : ℕ) :=
  {p : Fin (m + 1) × Fin (m + 1) // p.1 ≤ p.2}

/-- A deterministic sorted pair, with no selected finite enumeration. -/
def orderedPair {m : ℕ} (i j : Fin (m + 1)) : PairIndex m :=
  if h : i ≤ j then ⟨(i, j), h⟩ else ⟨(j, i), le_of_lt (lt_of_not_ge h)⟩

/-- A position for a quadratic monomial, with index zero representing the
constant coordinate. Thus `(0,0)` is constant and `(0,i)` is linear. -/
def pairWeight {m : ℕ} (p : PairIndex m) : ℕ :=
  weight m p.val.1 + weight m p.val.2

@[simp] theorem pairWeight_orderedPair {m : ℕ} (i j : Fin (m + 1)) :
    pairWeight (orderedPair i j) = weight m i + weight m j := by
  unfold orderedPair
  split
  · rfl
  · exact Nat.add_comm _ _

/-- Every canonical quadratic monomial receives its own exponent. -/
theorem pairWeight_injective (m : ℕ) : Function.Injective (pairWeight (m := m)) := by
  intro p q h
  rcases (weight_sum_eq_iff p.val.1 p.val.2 q.val.1 q.val.2).mp h with
    ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Subtype.ext (Prod.ext h1 h2)
  · have hp := p.property
    have hq := q.property
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem pairWeight_le {m : ℕ} (p : PairIndex m) :
    pairWeight p ≤ 4 * m ^ 3 + 2 * m ^ 2 + 2 * m :=
  weight_sum_le p.val.1 p.val.2

end DiophantineConsistency.SidonPositions
