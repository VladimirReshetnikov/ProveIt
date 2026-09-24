import Diophantine.Paper1980.Unit93

/-!
# The two binary unit tests (Section 6 of `BINARY_PRODUCT_90_PROOF.md`)

The two tested integers, each read with binary digits in radix `B = 2^mB ≥ 64`,
are `δ²` and `δ² + ⌊2x²/B⌋`, with `1 ≤ δ ≤ x < B`.  The first gives
`δ² = d₀ + d₁ B` with `d₀, d₁ ∈ {0, 1}`; if `d₀ = 1` then `δ² = 1 + d₁ B` and the
four square roots of one modulo a power of two leave `δ = 1`; otherwise
`δ² = B`, so `⌊2x²/B⌋ ≥ 2`, and the binary digits of `B + ⌊2x²/B⌋ < B²` force
`⌊2x²/B⌋ ≤ 1`, a contradiction.
-/

namespace Jones1980

namespace L90

/-- The two binary unit tests force `δ = 1`. -/
theorem unit_tests90 {B δ x : ℕ} (hB : 64 ≤ B) (hBpow : ∃ mB, B = 2 ^ mB) (hδ : 1 ≤ δ)
    (hδx : δ ≤ x) (hxB : x < B)
    (test1 : ∃ d0 d1 d2, d0 ≤ 1 ∧ d1 ≤ 1 ∧ d2 ≤ 1 ∧ δ ^ 2 = d0 + d1 * B + d2 * B ^ 2)
    (test2 : ∃ d0 d1 d2, d0 ≤ 1 ∧ d1 ≤ 1 ∧ d2 ≤ 1 ∧
      δ ^ 2 + 2 * x ^ 2 / B = d0 + d1 * B + d2 * B ^ 2) :
    δ = 1 := by
  obtain ⟨mB, hBm⟩ := hBpow
  have hδB : δ < B := lt_of_le_of_lt hδx hxB
  obtain ⟨d0, d1, d2, hd0, hd1, hd2, h1⟩ := test1
  have hd2z : d2 = 0 := by
    by_contra hne
    have h3 : B ^ 2 ≤ δ ^ 2 := by
      calc B ^ 2 = 1 * B ^ 2 := by ring
        _ ≤ d2 * B ^ 2 := Nat.mul_le_mul_right _ (by omega)
        _ ≤ δ ^ 2 := by rw [h1]; omega
    have : δ ^ 2 < B ^ 2 := Nat.pow_lt_pow_left hδB two_ne_zero
    omega
  rw [hd2z, zero_mul, add_zero] at h1
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd0 with rfl | rfl
  · -- `δ² = d₁ B`
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd1 with rfl | rfl
    · simp at h1; omega
    · rw [zero_add, one_mul] at h1
      exfalso
      have hxB2 : B ≤ x ^ 2 := by rw [← h1]; exact Nat.pow_le_pow_left hδx 2
      have hh2 : 2 ≤ 2 * x ^ 2 / B := by
        rw [Nat.le_div_iff_mul_le (by omega)]; omega
      have hh : 2 * x ^ 2 / B < 2 * B := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]
        have : x ^ 2 < B ^ 2 := Nat.pow_lt_pow_left hxB two_ne_zero
        nlinarith
      obtain ⟨e0, e1, e2, he0, he1, he2, h2⟩ := test2
      rw [h1] at h2
      have he2z : e2 = 0 := by
        by_contra hne
        have h3 : B ^ 2 ≤ B + 2 * x ^ 2 / B := by
          calc B ^ 2 = 1 * B ^ 2 := by ring
            _ ≤ e2 * B ^ 2 := Nat.mul_le_mul_right _ (by omega)
            _ ≤ _ := by rw [h2]; omega
        have h4 : B + 2 * x ^ 2 / B < 3 * B := by omega
        nlinarith
      rw [he2z, zero_mul, add_zero] at h2
      have : e1 * B ≤ B := by
        calc e1 * B ≤ 1 * B := Nat.mul_le_mul_right _ he1
          _ = B := one_mul B
      omega
  · -- `δ² = 1 + d₁ B`
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hd1 with rfl | rfl
    · have h2 : δ ^ 2 = 1 := by simpa using h1
      have : δ ≤ 1 := by nlinarith
      omega
    · rw [one_mul] at h1
      have hm : 6 ≤ mB := by
        by_contra h; push Not at h
        have : B < 64 := by
          rw [hBm]
          calc 2 ^ mB < 2 ^ 6 := Nat.pow_lt_pow_right (by norm_num) h
            _ = 64 := by norm_num
        omega
      have hB4 : B = 4 * 2 ^ (mB - 2) := by
        rw [hBm, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add]; congr 1; omega
      apply sqrt_one_mod_pow_two (k := mB - 2) (d := 1) (by omega) hδ ?_
        (by rw [h1, hB4]; ring)
      -- `δ < 2^(mB−2) = B/4`, since `δ² = B + 1 < (B/4)²`
      have h16 : 16 * (B + 1) < B ^ 2 := by nlinarith
      by_contra hge; push Not at hge
      have h3 : (2 ^ (mB - 2)) ^ 2 ≤ δ ^ 2 := Nat.pow_le_pow_left hge 2
      rw [h1] at h3
      have h4 : B ^ 2 = 16 * (2 ^ (mB - 2)) ^ 2 := by rw [hB4]; ring
      omega

end L90

end Jones1980
