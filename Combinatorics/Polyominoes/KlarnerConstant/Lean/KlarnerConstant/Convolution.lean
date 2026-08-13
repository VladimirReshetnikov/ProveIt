import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.NatAntidiagonal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Finite weighted-prefix bounds for positive-index Cauchy convolutions

This file is the exact finite-sum bridge used by the polyomino recurrence.
Sequences are functions `ℕ → ℚ`, but index zero is explicitly discarded by
`positivePart`; no hypothesis about the value supplied at index zero is needed.

`positiveWeightedPrefix ζ a N` is the inclusive positive-index sum

`∑ 1 ≤ n ≤ N, a n * ζ ^ n`.

The main results say that, for nonnegative sequences and `ζ ≥ 0`, the prefix
through `N + 1` of a two- or three-fold Cauchy convolution is bounded by the
product of the factor prefixes through `N`.  The one- and two-place shift
lemmas supply the factors of `ζ` and `ζ²` appearing in Bui's recurrences.
Everything here is a finite sum over rational numbers.
-/

namespace LeanProofs.KlarnerConstant

/-- Replace the coefficient at index zero by zero, leaving positive indices
unchanged.  This makes the positive-index convention independent of `a 0`. -/
def positivePart (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => a (n + 1)

@[simp] theorem positivePart_zero (a : ℕ → ℚ) : positivePart a 0 = 0 := rfl

@[simp] theorem positivePart_succ (a : ℕ → ℚ) (n : ℕ) :
    positivePart a (n + 1) = a (n + 1) := rfl

/-- Pointwise nonnegativity of a coefficient sequence. -/
def SequenceNonnegative (a : ℕ → ℚ) : Prop :=
  ∀ n, 0 ≤ a n

theorem positivePart_nonnegative {a : ℕ → ℚ} (ha : SequenceNonnegative a) :
    SequenceNonnegative (positivePart a) := by
  intro n
  cases n with
  | zero => simp
  | succ n => simpa using ha (n + 1)

/-- One weighted positive-index coefficient. -/
def positiveWeightedTerm (ζ : ℚ) (a : ℕ → ℚ) (n : ℕ) : ℚ :=
  positivePart a n * ζ ^ n

/-- The inclusive weighted prefix over positive indices `1, ..., N`. -/
def positiveWeightedPrefix (ζ : ℚ) (a : ℕ → ℚ) (N : ℕ) : ℚ :=
  ∑ n ∈ Finset.range (N + 1), positiveWeightedTerm ζ a n

@[simp] theorem positiveWeightedTerm_zero (ζ : ℚ) (a : ℕ → ℚ) :
    positiveWeightedTerm ζ a 0 = 0 := by
  simp [positiveWeightedTerm]

@[simp] theorem positiveWeightedPrefix_zero (ζ : ℚ) (a : ℕ → ℚ) :
    positiveWeightedPrefix ζ a 0 = 0 := by
  simp [positiveWeightedPrefix]

/-- When the supplied sequence already vanishes at zero, the positive prefix
is the ordinary `range (N + 1)` sum.  This is the adapter to exclusive-prefix
interfaces. -/
theorem positiveWeightedPrefix_eq_sum_range {ζ : ℚ} {a : ℕ → ℚ}
    (hzero : a 0 = 0) (N : ℕ) :
    positiveWeightedPrefix ζ a N =
      ∑ n ∈ Finset.range (N + 1), a n * ζ ^ n := by
  apply Finset.sum_congr rfl
  intro n _
  cases n with
  | zero => simp [positiveWeightedTerm, hzero]
  | succ n => simp [positiveWeightedTerm]

theorem positiveWeightedTerm_nonnegative {ζ : ℚ} (hζ : 0 ≤ ζ) {a : ℕ → ℚ}
    (ha : SequenceNonnegative a) (n : ℕ) :
    0 ≤ positiveWeightedTerm ζ a n := by
  exact mul_nonneg (positivePart_nonnegative ha n) (pow_nonneg hζ n)

theorem positiveWeightedPrefix_nonnegative {ζ : ℚ} (hζ : 0 ≤ ζ) {a : ℕ → ℚ}
    (ha : SequenceNonnegative a) (N : ℕ) :
    0 ≤ positiveWeightedPrefix ζ a N := by
  exact Finset.sum_nonneg fun n _ => positiveWeightedTerm_nonnegative hζ ha n

/-- Extending the inclusive endpoint adds exactly one weighted term. -/
theorem positiveWeightedPrefix_succ (ζ : ℚ) (a : ℕ → ℚ) (N : ℕ) :
    positiveWeightedPrefix ζ a (N + 1) =
      positiveWeightedPrefix ζ a N + positiveWeightedTerm ζ a (N + 1) := by
  simp [positiveWeightedPrefix, Finset.sum_range_succ, Nat.add_assoc]

/-- Nonnegative weighted prefixes are monotone in their endpoint. -/
theorem positiveWeightedPrefix_mono {ζ : ℚ} (hζ : 0 ≤ ζ) {a : ℕ → ℚ}
    (ha : SequenceNonnegative a) {M N : ℕ} (hMN : M ≤ N) :
    positiveWeightedPrefix ζ a M ≤ positiveWeightedPrefix ζ a N := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono (Nat.succ_le_succ hMN)
  · intro n _ _
    exact positiveWeightedTerm_nonnegative hζ ha n

/-- Pointwise comparison of nonnegative weights lifts to every positive
weighted prefix. -/
theorem positiveWeightedPrefix_mono_sequence {ζ : ℚ} (hζ : 0 ≤ ζ)
    {a b : ℕ → ℚ} (hab : ∀ n, a n ≤ b n) (N : ℕ) :
    positiveWeightedPrefix ζ a N ≤ positiveWeightedPrefix ζ b N := by
  apply Finset.sum_le_sum
  intro n _
  cases n with
  | zero => simp
  | succ n =>
      exact mul_le_mul_of_nonneg_right (hab (n + 1)) (pow_nonneg hζ (n + 1))

/-- Two-fold positive-index Cauchy convolution.  Terms with either index zero
vanish by construction. -/
def cauchyTwo (a b : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n,
    positivePart a ij.1 * positivePart b ij.2

/-- Three-fold positive-index Cauchy convolution, associated to the left. -/
def cauchyThree (a b c : ℕ → ℚ) : ℕ → ℚ :=
  cauchyTwo (cauchyTwo a b) c

@[simp] theorem cauchyTwo_zero (a b : ℕ → ℚ) : cauchyTwo a b 0 = 0 := by
  simp [cauchyTwo]

@[simp] theorem cauchyThree_zero (a b c : ℕ → ℚ) : cauchyThree a b c 0 = 0 := by
  simp [cauchyThree]

theorem cauchyTwo_nonnegative {a b : ℕ → ℚ}
    (ha : SequenceNonnegative a) (hb : SequenceNonnegative b) :
    SequenceNonnegative (cauchyTwo a b) := by
  intro n
  apply Finset.sum_nonneg
  intro ij _
  exact mul_nonneg (positivePart_nonnegative ha ij.1) (positivePart_nonnegative hb ij.2)

theorem cauchyThree_nonnegative {a b c : ℕ → ℚ}
    (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (hc : SequenceNonnegative c) :
    SequenceNonnegative (cauchyThree a b c) := by
  exact cauchyTwo_nonnegative (cauchyTwo_nonnegative ha hb) hc

/-- Weighting a convolution coefficient distributes its weight between the
two indices on the antidiagonal. -/
theorem positiveWeightedTerm_cauchyTwo (ζ : ℚ) (a b : ℕ → ℚ) (n : ℕ) :
    positiveWeightedTerm ζ (cauchyTwo a b) n =
      ∑ ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n,
        positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2 := by
  cases n with
  | zero => simp
  | succ n =>
      simp only [positiveWeightedTerm, positivePart_succ, cauchyTwo, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro ij hij
      have hsum : ij.1 + ij.2 = n + 1 :=
        Finset.HasAntidiagonal.mem_antidiagonal.mp hij
      rw [← hsum, pow_add]
      ring

/-- The square of index pairs whose coordinates are at most `bound`. -/
def pairSquare (bound : ℕ) : Finset (ℕ × ℕ) :=
  Finset.range (bound + 1) ×ˢ Finset.range (bound + 1)

/-- Pairs in `pairSquare bound` whose coordinate sum is at most `total`. -/
def pairRegion (bound total : ℕ) : Finset (ℕ × ℕ) :=
  (pairSquare bound).filter fun ij => ij.1 + ij.2 ≤ total

theorem antidiagonal_eq_pairSquare_filter {n N : ℕ} (hn : n ≤ N) :
    Finset.Nat.instHasAntidiagonal.antidiagonal n =
      (pairSquare N).filter (fun ij => ij.1 + ij.2 = n) := by
  ext ij
  simp only [Finset.HasAntidiagonal.mem_antidiagonal, Finset.mem_filter, pairSquare,
    Finset.mem_product, Finset.mem_range]
  constructor
  · intro hsum
    exact ⟨⟨by omega, by omega⟩, hsum⟩
  · rintro ⟨_, hsum⟩
    exact hsum

/-- Exact finite reindexing of a weighted convolution prefix as a triangular
sum of products. -/
theorem positiveWeightedPrefix_cauchyTwo_eq_pairRegion
    (ζ : ℚ) (a b : ℕ → ℚ) (N : ℕ) :
    positiveWeightedPrefix ζ (cauchyTwo a b) N =
      ∑ ij ∈ pairRegion N N,
        positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2 := by
  classical
  let term : ℕ × ℕ → ℚ := fun ij =>
    positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2
  calc
    positiveWeightedPrefix ζ (cauchyTwo a b) N =
        ∑ n ∈ Finset.range (N + 1),
          ∑ ij ∈ Finset.Nat.instHasAntidiagonal.antidiagonal n, term ij := by
      apply Finset.sum_congr rfl
      intro n _
      exact positiveWeightedTerm_cauchyTwo ζ a b n
    _ = ∑ n ∈ Finset.range (N + 1),
          ∑ ij ∈ (pairSquare N).filter (fun ij => ij.1 + ij.2 = n), term ij := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [antidiagonal_eq_pairSquare_filter (Nat.le_of_lt_succ (Finset.mem_range.mp hn))]
    _ = ∑ ij ∈ (pairSquare N).filter
          (fun ij => ij.1 + ij.2 ∈ Finset.range (N + 1)), term ij := by
      exact Finset.sum_fiberwise_eq_sum_filter
        (pairSquare N) (Finset.range (N + 1)) (fun ij => ij.1 + ij.2) term
    _ = ∑ ij ∈ pairRegion N N, term ij := by
      apply Finset.sum_congr
      · ext ij
        simp [pairRegion]
        omega
      · intro _ _
        rfl

/-- The triangular region through `N + 1` differs from the corresponding
region in the `N`-square only by boundary pairs with a zero coordinate, whose
positive-index weighted terms vanish. -/
theorem sum_pairRegion_succ_eq_sum_pairRegion
    (ζ : ℚ) (a b : ℕ → ℚ) (N : ℕ) :
    (∑ ij ∈ pairRegion (N + 1) (N + 1),
        positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2) =
      ∑ ij ∈ pairRegion N (N + 1),
        positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2 := by
  classical
  let term : ℕ × ℕ → ℚ := fun ij =>
    positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2
  have hsubset : pairRegion N (N + 1) ⊆ pairRegion (N + 1) (N + 1) := by
    intro ij hij
    simp only [pairRegion, pairSquare, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hij ⊢
    exact ⟨⟨by omega, by omega⟩, hij.2⟩
  symm
  apply Finset.sum_subset hsubset
  intro ij hij hnot
  have hzero : ij.1 = 0 ∨ ij.2 = 0 := by
    by_contra h
    have hi : 0 < ij.1 := Nat.pos_of_ne_zero (not_or.mp h).1
    have hj : 0 < ij.2 := Nat.pos_of_ne_zero (not_or.mp h).2
    apply hnot
    simp only [pairRegion, pairSquare, Finset.mem_filter, Finset.mem_product,
      Finset.mem_range] at hij ⊢
    exact ⟨⟨by omega, by omega⟩, hij.2⟩
  rcases hzero with hi | hj
  · simp [positiveWeightedTerm, hi]
  · simp [positiveWeightedTerm, hj]

/-- At the same endpoint, the convolution prefix is bounded by the product of
the two factor prefixes. -/
theorem positiveWeightedPrefix_cauchyTwo_le_product {ζ : ℚ} (hζ : 0 ≤ ζ)
    {a b : ℕ → ℚ} (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (N : ℕ) :
    positiveWeightedPrefix ζ (cauchyTwo a b) N ≤
      positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N := by
  rw [positiveWeightedPrefix_cauchyTwo_eq_pairRegion]
  calc
    (∑ ij ∈ pairRegion N N,
        positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2) ≤
        ∑ ij ∈ pairSquare N,
          positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro ij _ _
        exact mul_nonneg (positiveWeightedTerm_nonnegative hζ ha ij.1)
          (positiveWeightedTerm_nonnegative hζ hb ij.2)
    _ = positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N := by
      simp only [pairSquare, Finset.sum_product, positiveWeightedPrefix]
      rw [Finset.sum_mul_sum]

/-- The sharper positive-index estimate used in the recurrence induction: the
convolution prefix through `N + 1` already fits inside the product of the
factor prefixes through `N`. -/
theorem positiveWeightedPrefix_cauchyTwo_succ_le_product {ζ : ℚ} (hζ : 0 ≤ ζ)
    {a b : ℕ → ℚ} (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (N : ℕ) :
    positiveWeightedPrefix ζ (cauchyTwo a b) (N + 1) ≤
      positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N := by
  rw [positiveWeightedPrefix_cauchyTwo_eq_pairRegion,
    sum_pairRegion_succ_eq_sum_pairRegion]
  calc
    (∑ ij ∈ pairRegion N (N + 1),
        positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2) ≤
        ∑ ij ∈ pairSquare N,
          positiveWeightedTerm ζ a ij.1 * positiveWeightedTerm ζ b ij.2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.filter_subset _ _
      · intro ij _ _
        exact mul_nonneg (positiveWeightedTerm_nonnegative hζ ha ij.1)
          (positiveWeightedTerm_nonnegative hζ hb ij.2)
    _ = positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N := by
      simp only [pairSquare, Finset.sum_product, positiveWeightedPrefix]
      rw [Finset.sum_mul_sum]

/-- The corresponding three-fold bound, obtained without infinite series by
applying the two-fold finite-prefix estimates twice. -/
theorem positiveWeightedPrefix_cauchyThree_succ_le_product {ζ : ℚ} (hζ : 0 ≤ ζ)
    {a b c : ℕ → ℚ} (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (hc : SequenceNonnegative c) (N : ℕ) :
    positiveWeightedPrefix ζ (cauchyThree a b c) (N + 1) ≤
      positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N *
        positiveWeightedPrefix ζ c N := by
  calc
    positiveWeightedPrefix ζ (cauchyThree a b c) (N + 1) ≤
        positiveWeightedPrefix ζ (cauchyTwo a b) N *
          positiveWeightedPrefix ζ c N := by
      exact positiveWeightedPrefix_cauchyTwo_succ_le_product hζ
        (cauchyTwo_nonnegative ha hb) hc N
    _ ≤ (positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N) *
          positiveWeightedPrefix ζ c N := by
      exact mul_le_mul_of_nonneg_right
        (positiveWeightedPrefix_cauchyTwo_le_product hζ ha hb N)
        (positiveWeightedPrefix_nonnegative hζ hc N)

/-- Shift a positive-index sequence one place to the right. -/
def shiftOne (a : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => positivePart a n

/-- Shift a positive-index sequence two places to the right. -/
def shiftTwo (a : ℕ → ℚ) : ℕ → ℚ :=
  shiftOne (shiftOne a)

@[simp] theorem shiftOne_zero (a : ℕ → ℚ) : shiftOne a 0 = 0 := rfl

@[simp] theorem shiftOne_succ (a : ℕ → ℚ) (n : ℕ) :
    shiftOne a (n + 1) = positivePart a n := rfl

theorem shiftOne_nonnegative {a : ℕ → ℚ} (ha : SequenceNonnegative a) :
    SequenceNonnegative (shiftOne a) := by
  intro n
  cases n with
  | zero => simp
  | succ n => exact positivePart_nonnegative ha n

theorem shiftTwo_nonnegative {a : ℕ → ℚ} (ha : SequenceNonnegative a) :
    SequenceNonnegative (shiftTwo a) := by
  exact shiftOne_nonnegative (shiftOne_nonnegative ha)

@[simp] theorem positiveWeightedTerm_shiftOne_zero (ζ : ℚ) (a : ℕ → ℚ) :
    positiveWeightedTerm ζ (shiftOne a) 0 = 0 := by
  simp

@[simp] theorem positiveWeightedTerm_shiftOne_succ
    (ζ : ℚ) (a : ℕ → ℚ) (n : ℕ) :
    positiveWeightedTerm ζ (shiftOne a) (n + 1) =
      ζ * positiveWeightedTerm ζ a n := by
  simp only [positiveWeightedTerm, positivePart_succ, shiftOne_succ, pow_succ]
  ring

/-- Exact one-place shift identity for inclusive positive prefixes. -/
theorem positiveWeightedPrefix_shiftOne (ζ : ℚ) (a : ℕ → ℚ) (N : ℕ) :
    positiveWeightedPrefix ζ (shiftOne a) (N + 1) =
      ζ * positiveWeightedPrefix ζ a N := by
  unfold positiveWeightedPrefix
  rw [Finset.sum_range_succ']
  simp only [positiveWeightedTerm_shiftOne_zero, positiveWeightedTerm_shiftOne_succ,
    add_zero, Finset.mul_sum]

/-- Exact two-place shift identity. -/
theorem positiveWeightedPrefix_shiftTwo (ζ : ℚ) (a : ℕ → ℚ) (N : ℕ) :
    positiveWeightedPrefix ζ (shiftTwo a) (N + 2) =
      ζ ^ 2 * positiveWeightedPrefix ζ a N := by
  calc
    positiveWeightedPrefix ζ (shiftTwo a) (N + 2) =
        ζ * positiveWeightedPrefix ζ (shiftOne a) (N + 1) := by
      simpa [shiftTwo, Nat.add_assoc] using
        positiveWeightedPrefix_shiftOne ζ (shiftOne a) (N + 1)
    _ = ζ * (ζ * positiveWeightedPrefix ζ a N) := by
      rw [positiveWeightedPrefix_shiftOne]
    _ = ζ ^ 2 * positiveWeightedPrefix ζ a N := by ring

/-- At the induction endpoint `N + 1`, a two-place shift is bounded by `ζ²`
times the unshifted prefix through `N`. -/
theorem positiveWeightedPrefix_shiftTwo_succ_le {ζ : ℚ} (hζ : 0 ≤ ζ)
    {a : ℕ → ℚ} (ha : SequenceNonnegative a) (N : ℕ) :
    positiveWeightedPrefix ζ (shiftTwo a) (N + 1) ≤
      ζ ^ 2 * positiveWeightedPrefix ζ a N := by
  cases N with
  | zero =>
      norm_num [positiveWeightedPrefix, positiveWeightedTerm, positivePart, shiftTwo, shiftOne,
        Finset.sum_range_succ]
  | succ N =>
      calc
        positiveWeightedPrefix ζ (shiftTwo a) (Nat.succ N + 1) =
            ζ ^ 2 * positiveWeightedPrefix ζ a N := by
          simpa [Nat.succ_eq_add_one] using positiveWeightedPrefix_shiftTwo ζ a N
        _ ≤ ζ ^ 2 * positiveWeightedPrefix ζ a (Nat.succ N) := by
          exact mul_le_mul_of_nonneg_left
            (positiveWeightedPrefix_mono hζ ha (Nat.le_succ N)) (sq_nonneg ζ)

/-- A one-shifted convolution contributes `ζ` times at most the product of
the unshifted factor prefixes. -/
theorem positiveWeightedPrefix_shiftOne_cauchyTwo_succ_le {ζ : ℚ} (hζ : 0 ≤ ζ)
    {a b : ℕ → ℚ} (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (N : ℕ) :
    positiveWeightedPrefix ζ (shiftOne (cauchyTwo a b)) (N + 1) ≤
      ζ * (positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N) := by
  rw [positiveWeightedPrefix_shiftOne]
  exact mul_le_mul_of_nonneg_left
    (positiveWeightedPrefix_cauchyTwo_le_product hζ ha hb N) hζ

/-- A two-shifted convolution contributes `ζ²` times at most the product of
the unshifted factor prefixes. -/
theorem positiveWeightedPrefix_shiftTwo_cauchyTwo_succ_le {ζ : ℚ} (hζ : 0 ≤ ζ)
    {a b : ℕ → ℚ} (ha : SequenceNonnegative a) (hb : SequenceNonnegative b)
    (N : ℕ) :
    positiveWeightedPrefix ζ (shiftTwo (cauchyTwo a b)) (N + 1) ≤
      ζ ^ 2 *
        (positiveWeightedPrefix ζ a N * positiveWeightedPrefix ζ b N) := by
  exact (positiveWeightedPrefix_shiftTwo_succ_le hζ
    (cauchyTwo_nonnegative ha hb) N).trans <|
      mul_le_mul_of_nonneg_left
        (positiveWeightedPrefix_cauchyTwo_le_product hζ ha hb N) (sq_nonneg ζ)

end LeanProofs.KlarnerConstant
