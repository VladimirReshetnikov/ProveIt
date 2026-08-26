import FabiusFunction.ThueMorseOverlapFree

/-!
# Uniform recurrence of the Thue–Morse word, with an explicit linear bound

Every factor of the Thue–Morse word recurs in every window of bounded
length.  This module proves the atlas's uniform-recurrence proposition in
a form sharper than the text: the recurrence bound is explicit and
**linear** — a factor of length `ℓ ≤ 2^k` occurs in every window of
length `20·2^k`, so every factor of length `ℓ` recurs with gap at most
`40ℓ`.

The route is index arithmetic, not substitution machinery:

* `binaryWeight_block_concat` / `thueMorseBit_block_concat` — full block
  concatenation: `wt(q·2^k + r) = wt(q) + wt(r)` and
  `t(q·2^k + r) = t(q) ⊕ t(r)` for `r < 2^k`.  A window of length
  `ℓ ≤ 2^k` is therefore determined by its offset and the two block bits
  `(t(q₀), t(q₀+1))` of the aligned blocks it meets.
* `exists_thueMorseBit_eq` — among any three consecutive letters both
  values occur (no triples).
* `exists_thueMorseBit_pair` — **all four two-letter factors occur in
  every window of 17 letters**: pairs `(a, 1-a)` sit on even boundaries
  above a prescribed letter, and pairs `(a, a)` sit on odd boundaries
  above the pair `(1-a, a)`.
* `thueMorseBit_uniformly_recurrent` — the recurrence theorem: matching
  the two block bits inside any window reproduces the factor at the same
  offset.
-/

set_option autoImplicit false

open Finset

namespace Fabius

/-! ### Full block concatenation -/

/-- Binary weight of a block concatenation:
`wt(q·2^k + r) = wt(q) + wt(r)` for `r < 2^k`. -/
theorem binaryWeight_block_concat (k q r : ℕ) (hr : r < 2 ^ k) :
    binaryWeight (q * 2 ^ k + r) = binaryWeight q + binaryWeight r := by
  induction k generalizing r with
  | zero =>
      have : r = 0 := by omega
      subst this
      simp [binaryWeight]
  | succ k ih =>
      rcases Nat.even_or_odd' r with ⟨r', hr' | hr'⟩ <;> subst hr'
      · rw [show q * 2 ^ (k + 1) + 2 * r' = 2 * (q * 2 ^ k + r') by
          rw [pow_succ]; ring]
        rw [binaryWeight_two_mul, binaryWeight_two_mul,
          ih r' (by rw [pow_succ] at hr; omega)]
      · rw [show q * 2 ^ (k + 1) + (2 * r' + 1) = 2 * (q * 2 ^ k + r') + 1 by
          rw [pow_succ]; ring]
        rw [binaryWeight_two_mul_add_one, binaryWeight_two_mul_add_one,
          ih r' (by rw [pow_succ] at hr; omega)]
        omega

/-- Thue–Morse bit of a block concatenation:
`t(q·2^k + r) = (t(q) + t(r)) mod 2` for `r < 2^k`. -/
theorem thueMorseBit_block_concat (k q r : ℕ) (hr : r < 2 ^ k) :
    thueMorseBit (q * 2 ^ k + r) = (thueMorseBit q + thueMorseBit r) % 2 := by
  unfold thueMorseBit
  rw [binaryWeight_block_concat k q r hr, Nat.add_mod]

/-! ### Both letters and all pairs occur boundedly often -/

/-- Among any three consecutive letters, any prescribed value occurs. -/
theorem exists_thueMorseBit_eq (a n : ℕ) (ha : a ≤ 1) :
    ∃ j, j ≤ 2 ∧ thueMorseBit (n + j) = a := by
  have h0 := thueMorseBit_le_one n
  have h1 := thueMorseBit_le_one (n + 1)
  have h2 := thueMorseBit_le_one (n + 2)
  have htriple := thueMorseBit_no_triple n
  by_cases e0 : thueMorseBit n = a
  · exact ⟨0, by omega, by simpa using e0⟩
  · by_cases e1 : thueMorseBit (n + 1) = a
    · exact ⟨1, by omega, e1⟩
    · refine ⟨2, by omega, ?_⟩
      have : thueMorseBit n = thueMorseBit (n + 1) := by omega
      have : ¬ thueMorseBit (n + 1) = thueMorseBit (n + 2) := fun h =>
        htriple ⟨this, h⟩
      omega

/-- Pairs `(a, 1-a)` occur on even boundaries within seven letters. -/
theorem exists_thueMorseBit_pair_ne (a start : ℕ) (ha : a ≤ 1) :
    ∃ q, start ≤ q ∧ q + 1 ≤ start + 6 ∧
      thueMorseBit q = a ∧ thueMorseBit (q + 1) = 1 - a := by
  obtain ⟨j, hj, hbit⟩ := exists_thueMorseBit_eq a ((start + 1) / 2) ha
  refine ⟨2 * ((start + 1) / 2 + j), by omega, by omega, ?_, ?_⟩
  · rw [thueMorseBit_two_mul]
    exact hbit
  · rw [thueMorseBit_two_mul_add_one, hbit]

/-- **All four two-letter factors occur in every window of 17 letters.** -/
theorem exists_thueMorseBit_pair (a b start : ℕ) (ha : a ≤ 1) (hb : b ≤ 1) :
    ∃ q, start ≤ q ∧ q + 1 ≤ start + 16 ∧
      thueMorseBit q = a ∧ thueMorseBit (q + 1) = b := by
  rcases eq_or_ne b (1 - a) with hba | hba
  · obtain ⟨q, h1, h2, h3, h4⟩ := exists_thueMorseBit_pair_ne a start ha
    exact ⟨q, h1, by omega, h3, by omega⟩
  · -- b = a: place the pair on an odd boundary above (1-a, a)
    have hab : b = a := by omega
    subst hab
    obtain ⟨m, h1, h2, h3, h4⟩ :=
      exists_thueMorseBit_pair_ne (1 - b) ((start + 1) / 2) (by omega)
    refine ⟨2 * m + 1, by omega, by omega, ?_, ?_⟩
    · rw [thueMorseBit_two_mul_add_one, h3]
      omega
    · rw [show 2 * m + 1 + 1 = 2 * (m + 1) by ring, thueMorseBit_two_mul, h4]
      omega

/-! ### Uniform recurrence with a linear bound -/

/-- **Uniform recurrence, explicit and linear.**  A factor of length
`ℓ ≤ 2^k` starting anywhere occurs inside every window of length
`20·2^k`: it suffices to find, inside the window, an aligned block pair
carrying the same two block bits, and to reuse the same offset.  In
particular every factor of length `ℓ` recurs with gap at most `40·ℓ`. -/
theorem thueMorseBit_uniformly_recurrent (k ℓ i₀ start : ℕ) (hk : ℓ ≤ 2 ^ k) :
    ∃ i, start ≤ i ∧ i + ℓ ≤ start + 20 * 2 ^ k ∧
      ∀ j < ℓ, thueMorseBit (i + j) = thueMorseBit (i₀ + j) := by
  have hpow : 0 < 2 ^ k := Nat.two_pow_pos k
  obtain ⟨q, hq1, hq2, hqa, hqb⟩ :=
    exists_thueMorseBit_pair (thueMorseBit (i₀ / 2 ^ k))
      (thueMorseBit (i₀ / 2 ^ k + 1)) (start / 2 ^ k + 1)
      (thueMorseBit_le_one _) (thueMorseBit_le_one _)
  have hdm₀ := Nat.div_add_mod i₀ (2 ^ k)
  have hdms := Nat.div_add_mod start (2 ^ k)
  have hmod₀ : i₀ % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpow
  have hmods : start % 2 ^ k < 2 ^ k := Nat.mod_lt _ hpow
  -- product bookkeeping for omega
  have hmul1 : 2 ^ k * (start / 2 ^ k + 1) ≤ 2 ^ k * q :=
    Nat.mul_le_mul_left _ (by omega)
  have hmul2 : 2 ^ k * q ≤ 2 ^ k * (start / 2 ^ k + 16) :=
    Nat.mul_le_mul_left _ (by omega)
  have hexp1 : 2 ^ k * (start / 2 ^ k + 1) =
      2 ^ k * (start / 2 ^ k) + 2 ^ k := by ring
  have hexp2 : 2 ^ k * (start / 2 ^ k + 16) =
      2 ^ k * (start / 2 ^ k) + 16 * 2 ^ k := by ring
  refine ⟨2 ^ k * q + i₀ % 2 ^ k, by omega, by omega, ?_⟩
  intro j hj
  have hsplitq : (q + 1) * 2 ^ k = q * 2 ^ k + 2 ^ k := by ring
  have hsplitq₀ : (i₀ / 2 ^ k + 1) * 2 ^ k = (i₀ / 2 ^ k) * 2 ^ k + 2 ^ k := by
    ring
  rcases Nat.lt_or_ge (i₀ % 2 ^ k + j) (2 ^ k) with hcase | hcase
  · have hi : 2 ^ k * q + i₀ % 2 ^ k + j = q * 2 ^ k + (i₀ % 2 ^ k + j) := by
      ring
    have hi₀ : i₀ + j = (i₀ / 2 ^ k) * 2 ^ k + (i₀ % 2 ^ k + j) := by
      have : (i₀ / 2 ^ k) * 2 ^ k = 2 ^ k * (i₀ / 2 ^ k) := by ring
      omega
    rw [hi, hi₀, thueMorseBit_block_concat k q _ hcase,
      thueMorseBit_block_concat k _ _ hcase, hqa]
  · have hlt : i₀ % 2 ^ k + j - 2 ^ k < 2 ^ k := by omega
    have hi : 2 ^ k * q + i₀ % 2 ^ k + j =
        (q + 1) * 2 ^ k + (i₀ % 2 ^ k + j - 2 ^ k) := by
      have : (q + 1) * 2 ^ k = 2 ^ k * q + 2 ^ k := by ring
      omega
    have hi₀ : i₀ + j =
        (i₀ / 2 ^ k + 1) * 2 ^ k + (i₀ % 2 ^ k + j - 2 ^ k) := by
      have h1 : (i₀ / 2 ^ k + 1) * 2 ^ k = 2 ^ k * (i₀ / 2 ^ k) + 2 ^ k := by
        ring
      omega
    rw [hi, hi₀, thueMorseBit_block_concat k (q + 1) _ hlt,
      thueMorseBit_block_concat k _ _ hlt, hqb]

end Fabius
