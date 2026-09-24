import Diophantine.Paper1984.Identities
import Mathlib.Tactic

/-!
# Base-`Q` blocks

The 1984 paper describes a computation by numbers written to a base `Q`
(a power of two): `R_j = Σ_t r_{j,t} Q^t`, `L_i = Σ_t l_{i,t} Q^t`, (22)–(23).
This file collects the elementary facts about such numbers that the paper uses
tacitly:

* `blocks Q n f = Σ_{t<n} f t · Q^t`;
* the blocks of such a number can be read off again (`digit_blocks`), so two
  numbers with proper blocks (`< Q`) are equal iff their blocks are;
* for `Q = 2^q`, masking `≼` of numbers with proper blocks is blockwise
  masking (`mask_blocks_iff`), by iterating identity (13);
* when the block values are allowed to exceed `Q`, `normal` performs the carries
  (`blocks_normal`), and the carries stay `≤ 1` as long as the block values are
  `≤ 2Q - 2` (`carry_le_one`).
-/

namespace JM1984

open Finset

/-- `blocks Q n f = Σ_{t<n} f t · Q^t`. -/
def blocks (Q n : ℕ) (f : ℕ → ℕ) : ℕ := ∑ t ∈ range n, f t * Q ^ t

@[simp] theorem blocks_zero (Q : ℕ) (f : ℕ → ℕ) : blocks Q 0 f = 0 := by simp [blocks]

theorem blocks_succ (Q n : ℕ) (f : ℕ → ℕ) :
    blocks Q (n + 1) f = blocks Q n f + f n * Q ^ n := by
  simp [blocks, sum_range_succ]

/-- Peeling off the lowest block. -/
theorem blocks_succ' (Q n : ℕ) (f : ℕ → ℕ) :
    blocks Q (n + 1) f = f 0 + Q * blocks Q n (fun t => f (t + 1)) := by
  unfold blocks
  rw [sum_range_succ', mul_sum, add_comm]
  simp only [pow_zero, mul_one]
  congr 1
  apply sum_congr rfl
  intro t _
  ring

theorem blocks_congr {Q n : ℕ} {f g : ℕ → ℕ} (h : ∀ t < n, f t = g t) :
    blocks Q n f = blocks Q n g := by
  unfold blocks
  apply sum_congr rfl
  intro t ht
  rw [h t (mem_range.1 ht)]

theorem blocks_add (Q n : ℕ) (f g : ℕ → ℕ) :
    blocks Q n (fun t => f t + g t) = blocks Q n f + blocks Q n g := by
  simp [blocks, add_mul, sum_add_distrib]

theorem blocks_smul (Q n c : ℕ) (f : ℕ → ℕ) :
    blocks Q n (fun t => c * f t) = c * blocks Q n f := by
  simp [blocks, mul_sum, mul_assoc]

theorem blocks_sum {ι : Type*} (Q n : ℕ) (S : Finset ι) (g : ι → ℕ → ℕ) :
    blocks Q n (fun t => ∑ i ∈ S, g i t) = ∑ i ∈ S, blocks Q n (g i) := by
  simp only [blocks, sum_mul]
  exact sum_comm

theorem blocks_sub {Q n : ℕ} {f g : ℕ → ℕ} (h : ∀ t < n, g t ≤ f t) :
    blocks Q n (fun t => f t - g t) = blocks Q n f - blocks Q n g := by
  have : blocks Q n f = blocks Q n (fun t => f t - g t) + blocks Q n g := by
    rw [← blocks_add]
    apply blocks_congr
    intro t ht
    have := h t ht
    omega
  omega

/-- Multiplying by `Q` shifts the blocks up by one. -/
theorem blocks_shift (Q n : ℕ) (f : ℕ → ℕ) :
    Q * blocks Q n f = blocks Q (n + 1) (fun t => if t = 0 then 0 else f (t - 1)) := by
  rw [blocks_succ']
  simp

/-- A single block: `Q^k = blocks Q n (indicator k)` for `k < n`. -/
theorem blocks_single {Q n k : ℕ} (hk : k < n) :
    blocks Q n (fun t => if t = k then 1 else 0) = Q ^ k := by
  unfold blocks
  rw [sum_eq_single k]
  · simp
  · intro t _ ht; simp [ht]
  · intro h; exact absurd (mem_range.2 hk) h

theorem blocks_lt {Q n : ℕ} {f : ℕ → ℕ} (hf : ∀ t < n, f t < Q) : blocks Q n f < Q ^ n := by
  induction n generalizing f with
  | zero => simp
  | succ n ih =>
    rw [blocks_succ', pow_succ']
    have h0 := hf 0 (by omega)
    have hB := ih (f := fun t => f (t + 1)) (fun t ht => hf (t + 1) (by omega))
    calc f 0 + Q * blocks Q n (fun t => f (t + 1)) < Q + Q * blocks Q n (fun t => f (t + 1)) := by
          omega
      _ = Q * (blocks Q n (fun t => f (t + 1)) + 1) := by ring
      _ ≤ Q * Q ^ n := Nat.mul_le_mul_left _ hB

theorem blocks_of_zero_of_ge {Q n m : ℕ} {f : ℕ → ℕ} (hnm : n ≤ m) (hf : ∀ t, n ≤ t → f t = 0) :
    blocks Q m f = blocks Q n f := by
  unfold blocks
  rw [← sum_range_add_sum_Ico _ hnm]
  rw [sum_eq_zero (s := Ico n m)]
  · simp
  · intro t ht
    simp [hf t (mem_Ico.1 ht).1]

/-- The `t`-th base-`Q` block of `a`. -/
def digit (Q a t : ℕ) : ℕ := a / Q ^ t % Q

theorem digit_lt {Q : ℕ} (hQ : 0 < Q) (a t : ℕ) : digit Q a t < Q := Nat.mod_lt _ hQ

theorem digit_succ (Q a t : ℕ) : digit Q a (t + 1) = digit Q (a / Q) t := by
  simp [digit, Nat.div_div_eq_div_mul, pow_succ']

/-- The blocks of `blocks Q n f` are the `f t` (for `t < n`), when they are proper. -/
theorem digit_blocks {Q n : ℕ} (hQ : 0 < Q) {f : ℕ → ℕ} (hf : ∀ t < n, f t < Q) :
    ∀ t < n, digit Q (blocks Q n f) t = f t := by
  induction n generalizing f with
  | zero => intro t ht; omega
  | succ n ih =>
    intro t ht
    rw [blocks_succ']
    have hdiv : (f 0 + Q * blocks Q n (fun t => f (t + 1))) / Q = blocks Q n (fun t => f (t + 1)) := by
      rw [Nat.add_mul_div_left _ _ hQ, Nat.div_eq_of_lt (hf 0 (by omega)), Nat.zero_add]
    cases t with
    | zero =>
      simp only [digit, pow_zero, Nat.div_one]
      rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (hf 0 (by omega))]
    | succ t =>
      rw [digit_succ, hdiv]
      exact ih (f := fun t => f (t + 1)) (fun t ht => hf (t + 1) (by omega)) t (by omega)

/-- Every `a < Q^n` is the number with blocks `digit Q a t`. -/
theorem blocks_digit {Q n : ℕ} (hQ : 0 < Q) {a : ℕ} (ha : a < Q ^ n) :
    blocks Q n (digit Q a) = a := by
  induction n generalizing a with
  | zero => simp at ha; simp [ha]
  | succ n ih =>
    rw [blocks_succ']
    have : blocks Q n (fun t => digit Q a (t + 1)) = a / Q := by
      simp only [digit_succ]
      apply ih
      rw [Nat.div_lt_iff_lt_mul hQ, ← pow_succ]
      exact ha
    rw [this]
    simp [digit, Nat.mod_add_div]

/-- Numbers with proper blocks are equal iff their blocks are. -/
theorem blocks_eq_iff {Q n : ℕ} (hQ : 0 < Q) {f g : ℕ → ℕ} (hf : ∀ t < n, f t < Q)
    (hg : ∀ t < n, g t < Q) : blocks Q n f = blocks Q n g ↔ ∀ t < n, f t = g t := by
  constructor
  · intro h t ht
    rw [← digit_blocks hQ hf t ht, ← digit_blocks hQ hg t ht, h]
  · exact blocks_congr

theorem forall_lt_succ' {n : ℕ} {P : ℕ → Prop} :
    (∀ t < n + 1, P t) ↔ P 0 ∧ ∀ t < n, P (t + 1) := by
  constructor
  · intro h
    exact ⟨h 0 (by omega), fun t ht => h (t + 1) (by omega)⟩
  · rintro ⟨h0, h⟩ t ht
    cases t with
    | zero => exact h0
    | succ t => exact h t (by omega)

/-- Masking of numbers with proper base-`2^q` blocks is blockwise masking
(identity (13), iterated). -/
theorem mask_blocks_iff {q n : ℕ} {f g : ℕ → ℕ} (hf : ∀ t < n, f t < 2 ^ q)
    (hg : ∀ t < n, g t < 2 ^ q) :
    blocks (2 ^ q) n f ≼ blocks (2 ^ q) n g ↔ ∀ t < n, f t ≼ g t := by
  induction n generalizing f g with
  | zero =>
    simp only [blocks_zero]
    constructor
    · intro _ t ht; omega
    · intro _; exact Mask.refl 0
  | succ n ih =>
    rw [blocks_succ', blocks_succ', mul_comm (2 ^ q), mul_comm (2 ^ q),
      ← mask_add_pow_two_mul ⟨q, rfl⟩ (hf 0 (by omega)) (hg 0 (by omega)),
      ih (fun t ht => hf (t + 1) (by omega)) (fun t ht => hg (t + 1) (by omega)),
      forall_lt_succ']

/-- `a ≼ 2^k - 1 ↔ a < 2^k`. -/
theorem mask_two_pow_sub_one_iff (a k : ℕ) : a ≼ 2 ^ k - 1 ↔ a < 2 ^ k := by
  constructor
  · intro h
    have := h.le
    have hk : 0 < 2 ^ k := Nat.pow_pos (by norm_num)
    omega
  · intro h i hi
    rw [Nat.testBit_two_pow_sub_one]
    by_contra hc
    simp only [decide_eq_true_eq, not_lt] at hc
    have : a.testBit i = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) hc))
    rw [this] at hi
    exact Bool.false_ne_true hi

/-- A one-bit block is masked by `b` iff `b` is odd (when the block is `1`). -/
theorem mask_of_le_one_iff {a b : ℕ} (ha : a ≤ 1) : a ≼ b ↔ (a = 1 → b % 2 = 1) := by
  rw [mask_iff_div2]
  have : a / 2 = 0 := by omega
  rw [this]
  constructor
  · rintro ⟨h, -⟩ h1; exact h (by omega)
  · intro h; exact ⟨fun h1 => h (by omega), zero_mask _⟩

/-! ### Carries -/

/-- The carries produced when normalising block values `y t` (which may be `≥ Q`). -/
def carry (Q : ℕ) (y : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => (y t + carry Q y t) / Q

/-- The normalised (proper) blocks. -/
def normal (Q : ℕ) (y : ℕ → ℕ) (t : ℕ) : ℕ := (y t + carry Q y t) % Q

theorem normal_lt {Q : ℕ} (hQ : 0 < Q) (y : ℕ → ℕ) (t : ℕ) : normal Q y t < Q :=
  Nat.mod_lt _ hQ

@[simp] theorem carry_zero (Q : ℕ) (y : ℕ → ℕ) : carry Q y 0 = 0 := rfl

theorem carry_succ (Q : ℕ) (y : ℕ → ℕ) (t : ℕ) :
    carry Q y (t + 1) = (y t + carry Q y t) / Q := rfl

theorem blocks_normal (Q : ℕ) (y : ℕ → ℕ) (n : ℕ) :
    blocks Q n y = blocks Q n (normal Q y) + carry Q y n * Q ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [blocks_succ, blocks_succ, ih, carry_succ]
    unfold normal
    have h := Nat.div_add_mod (y n + carry Q y n) Q
    generalize (y n + carry Q y n) / Q = A at h ⊢
    generalize (y n + carry Q y n) % Q = B at h ⊢
    rw [pow_succ]
    zify at h ⊢
    linear_combination (-(Q : ℤ) ^ n) * h

/-- As long as the block values are `≤ 2Q - 2`, the carries are `≤ 1`. -/
theorem carry_le_one {Q : ℕ} (hQ : 0 < Q) {y : ℕ → ℕ} {n : ℕ}
    (hy : ∀ t < n, y t + 2 ≤ 2 * Q) : ∀ t ≤ n, carry Q y t ≤ 1 := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
    rw [carry_succ]
    have h1 := ih (by omega)
    have h2 := hy t (by omega)
    rw [Nat.div_le_iff_le_mul_add_pred hQ]
    omega

/-- The carry after a run of block values `≤ 2Q - 2` from position `1` on is still `≤ 1`
(the block value at position `0` is unrestricted below `2Q`). -/
theorem carry_le_one' {Q : ℕ} (hQ : 0 < Q) {y : ℕ → ℕ} {n : ℕ}
    (h0 : y 0 < 2 * Q) (hy : ∀ t, 1 ≤ t → t < n → y t + 2 ≤ 2 * Q) :
    ∀ t ≤ n, carry Q y t ≤ 1 := by
  intro t ht
  induction t with
  | zero => simp
  | succ t ih =>
    rw [carry_succ, Nat.div_le_iff_le_mul_add_pred hQ]
    have h1 := ih (by omega)
    rcases Nat.eq_zero_or_pos t with rfl | htpos
    · simp; omega
    · have h2 := hy t htpos (by omega)
      omega

end JM1984
