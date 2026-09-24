import Diophantine.Paper1980.DValid93
import Diophantine.Paper1980.MaskDigits

/-!
# Radix-`B` digits of explicit sums

Elementary facts used to read the masks of the 93-operation system digit by
digit: the digit of `Σ cᵢ Bⁱ` (with `cᵢ < B`) at position `k` is `c_k`; a
number below `B^N` is the sum of its `N` digits; `Σ_{i<k} (B − 1) Bⁱ + 1 = B^k`;
the digits of a residue modulo `B^k`; a base-`2^m` digit disjoint from
`2^m − 4` is at most three; and the indicator support lies below `K`.
-/

namespace Jones1980

namespace Iso

open Layout Finset

/-- The digit at `k` of `Σ_{i<N} cᵢ Bⁱ` is `c_k` (or `0` for `k ≥ N`). -/
theorem digit_sum {B : ℕ} (hB : 0 < B) :
    ∀ (k : ℕ) (c : ℕ → ℕ), (∀ i, c i < B) → ∀ N : ℕ,
      (∑ i ∈ range N, c i * B ^ i) / B ^ k % B = if k < N then c k else 0 := by
  intro k
  induction k with
  | zero =>
    intro c hc N
    rcases N with _ | N
    · simp
    · rw [Finset.sum_range_succ', if_pos (Nat.succ_pos N)]
      simp only [pow_zero, Nat.div_one, mul_one]
      have : ∑ i ∈ range N, c (i + 1) * B ^ (i + 1) = (∑ i ∈ range N, c (i + 1) * B ^ i) * B := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      rw [this, add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (hc 0)]
  | succ k ih =>
    intro c hc N
    rcases N with _ | N
    · simp
    · rw [Finset.sum_range_succ']
      simp only [pow_zero, mul_one]
      have : ∑ i ∈ range N, c (i + 1) * B ^ (i + 1) = (∑ i ∈ range N, c (i + 1) * B ^ i) * B := by
        rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; ring
      rw [this, add_comm, pow_succ', ← Nat.div_div_eq_div_mul, Nat.add_mul_div_right _ _ hB,
        Nat.div_eq_of_lt (hc 0), zero_add, ih (fun i => c (i + 1)) (fun i => hc (i + 1)) N]
      simp only [Nat.succ_lt_succ_iff]

/-- A number below `B^N` is the sum of its `N` digits. -/
theorem sum_digits {B : ℕ} (hB : 1 < B) :
    ∀ (N X : ℕ), X < B ^ N → ∑ i ∈ range N, (X / B ^ i % B) * B ^ i = X := by
  intro N
  induction N with
  | zero => intro X hX; simp at hX; simp [hX]
  | succ N ih =>
    intro X hX
    rw [Finset.sum_range_succ']
    simp only [pow_zero, Nat.div_one, mul_one]
    have e : ∀ i, X / B ^ (i + 1) = X / B / B ^ i := fun i => by
      rw [pow_succ', Nat.div_div_eq_div_mul]
    have hXB : X / B < B ^ N := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; rw [pow_succ] at hX; exact hX
    have : ∑ i ∈ range N, (X / B ^ (i + 1) % B) * B ^ (i + 1) =
        (∑ i ∈ range N, (X / B / B ^ i % B) * B ^ i) * B := by
      rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro i _; rw [e]; ring
    rw [this, ih (X / B) hXB, add_comm, Nat.mod_add_div' X B]

/-- `Σ_{i<k} (B − 1) Bⁱ + 1 = B^k`. -/
theorem sum_pred_mul_pow {B : ℕ} (hB : 1 ≤ B) :
    ∀ k : ℕ, ∑ i ∈ range k, (B - 1) * B ^ i + 1 = B ^ k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, add_right_comm, ih,
      show B ^ k + (B - 1) * B ^ k = (B - 1 + 1) * B ^ k by ring, Nat.sub_add_cancel hB, pow_succ']

/-- The digit at `i < k` of `N mod B^k` is the digit at `i` of `N`. -/
theorem digit_mod_pow (N B : ℕ) {i k : ℕ} (hik : i < k) :
    N % B ^ k / B ^ i % B = N / B ^ i % B := by
  rw [show B ^ k = B ^ i * B ^ (k - i) by rw [← pow_add]; congr 1; omega,
    Nat.mod_mul_right_div_self, Nat.mod_mod_of_dvd _ (dvd_pow_self B (by omega))]

/-- The top digit of a three-digit residue. -/
theorem digit_mod_pow_three_top (N B : ℕ) : N % B ^ 3 / B / B = N / B ^ 2 % B := by
  rw [Nat.div_div_eq_div_mul, show B ^ 3 = B * B * B by ring, Nat.mod_mul_right_div_self,
    pow_two]

/-- A base-`2^m` digit disjoint from `2^m − 4` is at most three. -/
theorem le_three_of_land {x m : ℕ} (hm : 2 ≤ m) (hx : x < 2 ^ m) (h : x &&& (2 ^ m - 4) = 0) :
    x ≤ 3 := by
  have h1 : (x &&& (2 ^ m - 4)) >>> 2 = 0 := by rw [h]; rfl
  rw [Nat.shiftRight_and_distrib, Nat.shiftRight_eq_div_pow, Nat.shiftRight_eq_div_pow] at h1
  have e : 2 ^ m = 2 ^ (m - 2) * 2 ^ 2 := by rw [← pow_add]; congr 1; omega
  have h2 : (2 ^ m - 4) / 2 ^ 2 = 2 ^ (m - 2) - 1 := by
    rw [e, show (4 : ℕ) = 1 * 2 ^ 2 by norm_num, ← Nat.sub_mul, Nat.mul_div_cancel _ (by norm_num)]
  rw [h2] at h1
  have h3 : x / 2 ^ 2 < 2 ^ (m - 2) := by
    rw [Nat.div_lt_iff_lt_mul (by norm_num)]; rw [e] at hx; exact hx
  rw [Nat.and_two_pow_sub_one_of_lt_two_pow h3] at h1
  norm_num at h1
  omega

section Supp

variable {m s : ℕ}

/-- The indicator support lies below `K`. -/
theorem mem_supp_lt {h : ℕ} (hh : h ∈ supp m s) : h < K m s := by
  unfold supp at hh; unfold K
  rw [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion] at hh
  rcases hh with ⟨i, hi, rfl⟩ | ⟨j, hj, hj'⟩
  · have := v_le_M (Finset.mem_range.1 hi); have := t_ge_two_M m s (s - 1); omega
  · simp only [Finset.mem_insert, Finset.mem_singleton] at hj'
    have := t_mono (m := m) (s := s) (show j ≤ s - 1 by have := Finset.mem_range.1 hj; omega)
    omega

theorem ind_eq_zero_of_ge {h : ℕ} (hh : K m s ≤ h) : ind m s h = 0 := by
  unfold ind
  rw [if_neg]
  intro hmem
  have := mem_supp_lt hmem
  omega

theorem ind_eq_one_iff (h : ℕ) : ind m s h = 1 ↔ h ∈ supp m s := by
  unfold ind; split_ifs with hh <;> simp [hh]

theorem ind_eq_zero_iff (h : ℕ) : ind m s h = 0 ↔ h ∉ supp m s := by
  unfold ind; split_ifs with hh <;> simp [hh]

end Supp

end Iso

end Jones1980
