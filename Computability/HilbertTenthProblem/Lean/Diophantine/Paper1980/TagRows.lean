import Diophantine.Paper1980.TernaryDigits
import Mathlib.Algebra.Ring.GeomSum

/-!
# Rows of a ternary word and the row-head word

The packed words of the tag-system route are read in rows of `m` ternary digits
(`R = 3^m` is the counter radix): position `p = m·i + k` is the offset `k` of row `i`.
This file provides

* `row X m i = X / R^i mod R`, the `i`-th row, with `dg (row X m i) k = dg X (m i + k)`;
* the row-head word `heads m t = Σ_{i<t} R^i` with the geometric identity
  `heads m t · (R − 1) + 1 = R^t` and its digits (a `1` exactly at the heads `m·i`,
  `i < t`), and the shifted heads `3^α · heads m t` (a `1` at offset `α` of every row);
* the radix geometry: if `3^m − 1 ∣ 3^e − 1` with `m ≥ 1` then `m ∣ e`
  (`dvd_of_pow_sub_one_dvd`), so a solution of `H(R − 1) = q − 1` with `q = 3^e`,
  `R = 3^m` has `q = R^t` and `H = heads m t`.
-/

namespace Jones1980

namespace Ternary

open Finset

/-! ### Rows -/

/-- The `i`-th row of `m` digits. -/
def row (X m i : ℕ) : ℕ := X / 3 ^ (m * i) % 3 ^ m

theorem row_lt (X m i : ℕ) : row X m i < 3 ^ m := Nat.mod_lt _ (by positivity)

theorem dg_row {k m : ℕ} (X i : ℕ) (hk : k < m) : dg (row X m i) k = dg X (m * i + k) := by
  rw [row, dg_mod_pow_of_lt _ hk, dg_div_pow]

theorem dg_row_of_ge {k m : ℕ} (X i : ℕ) (hk : m ≤ k) : dg (row X m i) k = 0 := by
  rw [row, dg_mod_pow_of_ge _ hk]

theorem Bool3.row {X : ℕ} (hX : Bool3 X) (m i : ℕ) : Bool3 (row X m i) :=
  (hX.div_pow _).mod_pow _

theorem row_eq_zero_of_lt {X m i : ℕ} (h : X < 3 ^ (m * i)) : row X m i = 0 := by
  rw [row, Nat.div_eq_of_lt h]; simp

/-- Two words with the same rows below `t` and both below `R^t` are equal. -/
theorem eq_of_rows {X Y m t : ℕ} (hX : X < 3 ^ (m * t)) (hY : Y < 3 ^ (m * t))
    (h : ∀ i, i < t → row X m i = row Y m i) : X = Y := by
  have hd : ∀ p, dg X p = dg Y p := by
    intro p
    rcases Nat.lt_or_ge p (m * t) with hp | hp
    · have hm : 0 < m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0; simp at hp
        · exact h0
      have hi : p / m < t := by
        rw [Nat.div_lt_iff_lt_mul hm]; linarith [Nat.mul_comm m t]
      have e : p = m * (p / m) + p % m := (Nat.div_add_mod p m).symm
      rw [e, ← dg_row X (p / m) (Nat.mod_lt _ hm), ← dg_row Y (p / m) (Nat.mod_lt _ hm), h _ hi]
    · rw [dg_eq_zero_of_lt (lt_of_lt_of_le hX (Nat.pow_le_pow_right (by norm_num) hp)),
        dg_eq_zero_of_lt (lt_of_lt_of_le hY (Nat.pow_le_pow_right (by norm_num) hp))]
  have hn : ∀ n, X < 3 ^ n → Y < 3 ^ n → X = Y := by
    intro n hXn hYn
    rw [← val_dg hXn, ← val_dg hYn]
    unfold val
    exact sum_congr rfl fun p _ => by rw [hd p]
  exact hn (m * t) hX hY

/-- The rows of `X mod R^t` below `t` are the rows of `X`. -/
theorem row_mod_pow {X m t i : ℕ} (hi : i < t) : row (X % 3 ^ (m * t)) m i = row X m i := by
  unfold row
  have e : m * t = m * i + m * (t - i) := by rw [← Nat.mul_add, Nat.add_sub_cancel' hi.le]
  rw [e, pow_add, Nat.mod_mul_right_div_self]
  have hdvd : 3 ^ m ∣ 3 ^ (m * (t - i)) := Nat.pow_dvd_pow 3 (Nat.le_mul_of_pos_right _ (by omega))
  rw [Nat.mod_mod_of_dvd _ hdvd]

/-- A word below `R^t` is the sum of its rows. -/
theorem sum_rows {X m : ℕ} : ∀ t, X < 3 ^ (m * t) → X = ∑ i ∈ range t, row X m i * 3 ^ (m * i)
  | 0, h => by simp at h; simp [h]
  | t + 1, h => by
    rw [sum_range_succ]
    have hsplit := Nat.div_add_mod X (3 ^ (m * t))
    have hrow : row X m t = X / 3 ^ (m * t) := by
      unfold row
      apply Nat.mod_eq_of_lt
      rw [Nat.div_lt_iff_lt_mul (by positivity), ← pow_add, show m + m * t = m * (t + 1) by ring]
      exact h
    have hmod : X % 3 ^ (m * t) < 3 ^ (m * t) := Nat.mod_lt _ (by positivity)
    have ih := sum_rows t hmod
    have hrows : ∑ i ∈ range t, row (X % 3 ^ (m * t)) m i * 3 ^ (m * i) =
        ∑ i ∈ range t, row X m i * 3 ^ (m * i) :=
      sum_congr rfl fun i hi => by rw [row_mod_pow (mem_range.1 hi)]
    rw [hrows] at ih
    rw [← ih, hrow]
    have : X / 3 ^ (m * t) * 3 ^ (m * t) = 3 ^ (m * t) * (X / 3 ^ (m * t)) := mul_comm _ _
    omega

/-! ### The row-head word -/

/-- The row-head word `Σ_{i<t} R^i`, `R = 3^m`. -/
def heads (m t : ℕ) : ℕ := ∑ i ∈ range t, 3 ^ (m * i)

theorem heads_zero (m : ℕ) : heads m 0 = 0 := by simp [heads]

theorem heads_succ (m t : ℕ) : heads m (t + 1) = heads m t + 3 ^ (m * t) := by
  simp [heads, sum_range_succ]

theorem heads_succ' (m t : ℕ) : heads m (t + 1) = 1 + 3 ^ m * heads m t := by
  unfold heads
  rw [sum_range_succ', mul_sum]
  simp only [mul_zero, pow_zero]
  rw [add_comm]
  congr 1
  exact sum_congr rfl fun i _ => by rw [← pow_add]; congr 1; ring

theorem heads_mul (m : ℕ) : ∀ t, heads m t * 3 ^ m + 1 = 3 ^ (m * t) + heads m t
  | 0 => by simp [heads_zero]
  | t + 1 => by
    have ih := heads_mul m t
    rw [heads_succ', show m * (t + 1) = m * t + m by ring, pow_add]
    have ihZ : ((heads m t : ℕ) : ℤ) * 3 ^ m + 1 = 3 ^ (m * t) + heads m t := by
      exact_mod_cast ih
    have : ((1 + 3 ^ m * heads m t : ℕ) : ℤ) * 3 ^ m + 1 =
        3 ^ (m * t) * 3 ^ m + ((1 + 3 ^ m * heads m t : ℕ) : ℤ) := by
      push_cast; linear_combination (3 : ℤ) ^ m * ihZ
    exact_mod_cast this

/-- The geometric identity `heads m t · (R − 1) + 1 = R^t`. -/
theorem heads_mul_sub_one (m t : ℕ) : heads m t * (3 ^ m - 1) + 1 = 3 ^ (m * t) := by
  rw [Nat.mul_sub, mul_one]
  have := heads_mul m t
  have : 1 ≤ 3 ^ (m * t) := Nat.one_le_pow _ _ (by norm_num)
  omega

theorem heads_lt (m t : ℕ) (hm : 1 ≤ m) : heads m t < 3 ^ (m * t) := by
  have := heads_mul_sub_one m t
  have h1 : 2 ≤ 3 ^ m := by
    calc 2 ≤ 3 ^ 1 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have h2 : heads m t ≤ heads m t * (3 ^ m - 1) := Nat.le_mul_of_pos_right _ (by omega)
  omega

/-- The digits of the row-head word: a `1` exactly at the heads `m·i`, `i < t`. -/
theorem dg_heads {m : ℕ} (hm : 1 ≤ m) (t p : ℕ) :
    dg (heads m t) p = if p % m = 0 ∧ p < m * t then 1 else 0 := by
  induction t generalizing p with
  | zero => simp [heads_zero]
  | succ t ih =>
    rw [heads_succ]
    rcases Nat.lt_or_ge p (m * t) with hp | hp
    · rw [← mul_one (3 ^ (m * t)), mul_comm, dg_add_mul_pow hp, ih]
      have : p < m * (t + 1) := by nlinarith
      simp [hp, this]
    · have hh : heads m t < 3 ^ (m * t) := heads_lt m t hm
      have hd : dg (heads m t + 3 ^ (m * t)) p = dg (heads m t) p + dg (3 ^ (m * t)) p := by
        apply dg_add_of_le_two
        intro p'
        have := bool3_pow (m * t) p'
        have h0 : dg (heads m t) p' ≤ 1 := by
          rw [ih p']; split_ifs <;> omega
        omega
      rw [hd, dg_eq_zero_of_lt (lt_of_lt_of_le hh (Nat.pow_le_pow_right (by norm_num) hp)),
        dg_pow, zero_add]
      by_cases hpt : p = m * t
      · subst hpt
        simp [Nat.mul_mod_right, show m * t < m * (t + 1) by nlinarith]
      · rw [if_neg hpt]
        by_cases hlt : p < m * (t + 1)
        · have hmod : p % m ≠ 0 := by
            intro h0
            obtain ⟨c, hc⟩ : ∃ c, p = m * c := ⟨p / m, by
              have := Nat.div_add_mod p m; omega⟩
            subst hc
            have hc1 : t ≤ c := by
              by_contra h; push Not at h
              have : m * c < m * t := Nat.mul_lt_mul_of_pos_left h (by omega)
              omega
            have hc2 : c < t + 1 := by
              by_contra h; push Not at h
              have : m * (t + 1) ≤ m * c := Nat.mul_le_mul_left _ h
              omega
            exact hpt (by rw [show c = t by omega])
          simp [hmod]
        · simp [hlt]

theorem bool3_heads {m : ℕ} (hm : 1 ≤ m) (t : ℕ) : Bool3 (heads m t) := fun p => by
  rw [dg_heads hm]; split_ifs <;> omega

/-- The rows of the head word. -/
theorem row_heads {m : ℕ} (hm : 1 ≤ m) {t i : ℕ} (hi : i < t) : row (heads m t) m i = 1 := by
  have h1 : ∀ k, dg (row (heads m t) m i) k = dg 1 k := by
    intro k
    rcases Nat.lt_or_ge k m with hk | hk
    · rw [dg_row _ _ hk, dg_heads hm]
      rcases Nat.eq_zero_or_pos k with h0 | h0
      · subst h0
        simp [Nat.mul_mod_right, dg_zero_pos, show m * i < m * t by nlinarith]
      · have e : (m * i + k) % m = k := by
          rw [add_comm, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk]
        have : dg 1 k = 0 := dg_eq_zero_of_lt (by
          calc 1 < 3 ^ 1 := by norm_num
            _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) h0)
        rw [this, e, if_neg (by omega)]
    · rw [dg_row_of_ge _ _ hk, dg_eq_zero_of_lt (by
        calc 1 < 3 ^ 1 := by norm_num
          _ ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega))]
  have h2 : row (heads m t) m i < 3 ^ m := row_lt _ _ _
  have h3 : 1 < 3 ^ m := by
    calc 1 < 3 ^ 1 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  rw [← val_dg h2, ← val_dg h3]
  unfold val
  exact sum_congr rfl fun p _ => by rw [h1 p]

/-! ### Radix geometry -/

/-- If `3^m − 1 ∣ 3^e − 1` with `m ≥ 1`, then `m ∣ e`. -/
theorem dvd_of_pow_sub_one_dvd {m e : ℕ} (hm : 1 ≤ m) (h : 3 ^ m - 1 ∣ 3 ^ e - 1) : m ∣ e := by
  obtain ⟨t, s, hs, rfl⟩ : ∃ t s, s < m ∧ e = m * t + s :=
    ⟨e / m, e % m, Nat.mod_lt _ (by omega), (Nat.div_add_mod e m).symm⟩
  have h1 : 3 ^ m - 1 ∣ (3 ^ m) ^ t - 1 := Nat.sub_one_dvd_pow_sub_one (3 ^ m) t
  have h2 : 3 ^ (m * t + s) - 1 = 3 ^ s * ((3 ^ m) ^ t - 1) + (3 ^ s - 1) := by
    rw [pow_add, pow_mul, Nat.mul_sub, mul_one]
    have ha : 1 ≤ (3 ^ m) ^ t := Nat.one_le_pow _ _ (by positivity)
    have hb : 1 ≤ 3 ^ s := Nat.one_le_pow _ _ (by norm_num)
    have hc : 3 ^ s ≤ 3 ^ s * (3 ^ m) ^ t := Nat.le_mul_of_pos_right _ (by positivity)
    have e : (3 ^ m) ^ t * 3 ^ s = 3 ^ s * (3 ^ m) ^ t := mul_comm _ _
    omega
  have h3 : 3 ^ m - 1 ∣ 3 ^ s - 1 := by
    have h4 : 3 ^ m - 1 ∣ 3 ^ s * ((3 ^ m) ^ t - 1) := Dvd.dvd.mul_left h1 _
    have := (Nat.dvd_add_right h4).1 (h2 ▸ h)
    exact this
  have h5 : 3 ^ s - 1 < 3 ^ m - 1 := by
    have : 3 ^ s < 3 ^ m := Nat.pow_lt_pow_right (by norm_num) hs
    have : 1 ≤ 3 ^ s := Nat.one_le_pow _ _ (by norm_num)
    omega
  have h6 : 3 ^ s - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h3 h5
  have h7 : s = 0 := by
    rcases Nat.eq_zero_or_pos s with h | h
    · exact h
    · exfalso
      have : 3 ^ 1 ≤ 3 ^ s := Nat.pow_le_pow_right (by norm_num) h
      omega
  subst h7
  exact ⟨t, by ring⟩

/-- The head equation `H(R − 1) = q − 1` with `q = 3^e`, `R = 3^m`, `m ≥ 1`: then
`q = R^t` and `H = heads m t` for `t = e / m`. -/
theorem heads_of_head_eq {H m e : ℕ} (hm : 1 ≤ m) (hH : H * (3 ^ m - 1) = 3 ^ e - 1) :
    ∃ t, e = m * t ∧ H = heads m t := by
  have hdvd : 3 ^ m - 1 ∣ 3 ^ e - 1 := ⟨H, by rw [← hH]; ring⟩
  obtain ⟨t, ht⟩ := dvd_of_pow_sub_one_dvd hm hdvd
  refine ⟨t, ht, ?_⟩
  have h1 := heads_mul_sub_one m t
  rw [← ht] at h1
  have h2 : 1 ≤ 3 ^ e := Nat.one_le_pow _ _ (by norm_num)
  have h3 : H * (3 ^ m - 1) = heads m t * (3 ^ m - 1) := by omega
  have h4 : 0 < 3 ^ m - 1 := by
    have : 3 ^ 1 ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    omega
  exact Nat.eq_of_mul_eq_mul_right h4 h3

end Ternary

end Jones1980
