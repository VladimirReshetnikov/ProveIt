import Diophantine.Paper1980.CodeDigits

/-!
# The three unit tests force `δ = 1` (Section 6)

The homogeneous coordinate `δ` satisfies `1 ≤ δ ≤ x < B` with `B ≥ 64` a power
of two.  The three unpaired targets show, as three-digit numbers with digits
`≤ 3`, the values `δ²`, `δ² + ⌊5x²/B⌋` and `δ² + ⌊7x²/B⌋`.  Then `δ = 1`:

* `δ² = d₀ + d₁ B` with `d₀ ∈ {0, 1}` (a square modulo four);
* if `d₀ = 1` then `δ < B/4` and `δ² ≡ 1 (mod B)`; the square roots of one
  modulo a power of two below `B/4` reduce to `δ = 1` (`u(u+1) = d₁ B/4` with
  `δ = 2u + 1` and coprime `u, u + 1`);
* if `d₀ = 0` then `B ≤ δ² ≤ x²`, so `⌊5x²/B⌋ ≥ 5`, while the two padded tests
  force `⌊5x²/B⌋ = m₅ B + r₅`, `⌊7x²/B⌋ = m₇ B + r₇` with `r₅, r₇ ≤ 3`,
  `m₅, m₇ ≤ 2`, and `7⌊5x²/B⌋ − 5⌊7x²/B⌋ ∈ (−7, 5)` forces `m₅ = m₇ = 0`,
  a contradiction.
-/

namespace Jones1980

/-- A square is `0` or `1` modulo four. -/
theorem sq_mod_four (δ : ℕ) : δ ^ 2 % 4 = 0 ∨ δ ^ 2 % 4 = 1 := by
  rw [Nat.pow_mod]
  have h4 : δ % 4 < 4 := Nat.mod_lt _ (by norm_num)
  interval_cases δ % 4 <;> simp

/-- `δ² ≡ 1 (mod 2^k)` with `1 ≤ δ < 2^k` and `k ≥ 1` forces `δ = 1`. -/
theorem sqrt_one_mod_pow_two {k δ d : ℕ} (hk : 1 ≤ k) (hδ : 1 ≤ δ) (hδk : δ < 2 ^ k)
    (h : δ ^ 2 = 1 + 4 * (d * 2 ^ k)) : δ = 1 := by
  -- `δ` is odd
  have hodd : δ % 2 = 1 := by
    have h2 : δ * δ % 2 = 1 := by rw [← sq, h]; omega
    have := Nat.mod_lt δ (show 0 < 2 by norm_num)
    rw [Nat.mul_mod] at h2
    interval_cases hd : δ % 2
    · simp at h2
    · rfl
  obtain ⟨u, hu⟩ : ∃ u, δ = 2 * u + 1 := ⟨δ / 2, by omega⟩
  have hu2 : u * (u + 1) = d * 2 ^ k := by
    rw [hu] at h; ring_nf at h ⊢; omega
  have hdvd : 2 ^ k ∣ u * (u + 1) := by rw [hu2]; exact Dvd.intro_left _ rfl
  have hcop : Nat.Coprime u (u + 1) := Nat.coprime_self_add_right.2 (Nat.coprime_one_right u)
  have hpp : IsPrimePow (2 ^ k) := (Nat.prime_two.prime.isPrimePow).pow (by omega)
  rcases (hcop.isPrimePow_dvd_mul hpp).1 hdvd with hd | hd
  · have : u = 0 := Nat.eq_zero_of_dvd_of_lt hd (by omega)
    omega
  · have := Nat.le_of_dvd (by omega) hd
    omega

/-- A padded unit test with `δ² = d₁ B`: the carry `h < cB` (`c ≤ 7`) has `h mod B ≤ 3` and
`d₁ + ⌊h / B⌋ ≤ 3`. -/
theorem padded_test {B δ d1 c h : ℕ} (hB : 64 ≤ B) (hd1 : d1 ≤ 3) (hc7 : c ≤ 7)
    (h1 : δ ^ 2 = d1 * B) (hlt : h < c * B)
    (test : ∃ e0 e1 e2, e0 ≤ 3 ∧ e1 ≤ 3 ∧ e2 ≤ 3 ∧ δ ^ 2 + h = e0 + e1 * B + e2 * B ^ 2) :
    h % B ≤ 3 ∧ d1 + h / B ≤ 3 := by
  obtain ⟨e0, e1, e2, he0, he1, he2, heq⟩ := test
  have hB2 : 10 * B < B ^ 2 := by nlinarith
  have hcB : c * B ≤ 7 * B := Nat.mul_le_mul_right _ hc7
  have hdB : d1 * B ≤ 3 * B := Nat.mul_le_mul_right _ hd1
  have hsmall : δ ^ 2 + h < B ^ 2 := by rw [h1]; linarith
  have he2z : e2 = 0 := by
    by_contra hne
    have : B ^ 2 ≤ e2 * B ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [he2z] at heq
  have hmod := Nat.mod_add_div h B
  have heq' : h % B + (d1 + h / B) * B = e0 + e1 * B := by
    have e : δ ^ 2 + h = h % B + (d1 + h / B) * B := by rw [h1]; linarith
    rw [← e, heq]; ring
  obtain ⟨ha, hb⟩ := split_code (by omega) (Nat.mod_lt _ (by omega)) (by omega) heq'
  omega

/-- The two carries `h₅ = m₅ B + r₅`, `h₇ = m₇ B + r₇` with `r ≤ 3`, `m ≤ 2`, `h₅ ≥ 5`,
`7h₅ < 5h₇ + 5` and `5h₇ < 7h₅ + 7` are contradictory. -/
theorem carry_contra {B h5 h7 m5 m7 r5 r7 : ℕ} (hB : 64 ≤ B)
    (e5 : h5 = B * m5 + r5) (e7 : h7 = B * m7 + r7) (hr5 : r5 ≤ 3) (hr7 : r7 ≤ 3)
    (hm5 : m5 ≤ 2) (hm7 : m7 ≤ 2) (hge : 5 ≤ h5)
    (hA : 7 * h5 < 5 * h7 + 5) (hB' : 5 * h7 < 7 * h5 + 7) : False := by
  subst e5 e7
  interval_cases m5 <;> interval_cases m7 <;> omega

set_option maxHeartbeats 1000000 in
/-- The three unit tests force `δ = 1`. -/
theorem unit_tests {B δ x : ℕ} (hB : 64 ≤ B) (hBpow : ∃ mB, B = 2 ^ mB) (hδ : 1 ≤ δ)
    (hδx : δ ≤ x) (hxB : x < B)
    (test1 : ∃ d0 d1 d2, d0 ≤ 3 ∧ d1 ≤ 3 ∧ d2 ≤ 3 ∧ δ ^ 2 = d0 + d1 * B + d2 * B ^ 2)
    (test5 : ∃ d0 d1 d2, d0 ≤ 3 ∧ d1 ≤ 3 ∧ d2 ≤ 3 ∧
      δ ^ 2 + 5 * x ^ 2 / B = d0 + d1 * B + d2 * B ^ 2)
    (test7 : ∃ d0 d1 d2, d0 ≤ 3 ∧ d1 ≤ 3 ∧ d2 ≤ 3 ∧
      δ ^ 2 + 7 * x ^ 2 / B = d0 + d1 * B + d2 * B ^ 2) :
    δ = 1 := by
  obtain ⟨mB, hBm⟩ := hBpow
  obtain ⟨k, rfl⟩ : ∃ k, mB = k + 2 := by
    refine ⟨mB - 2, ?_⟩
    by_contra h
    have : mB < 2 := by omega
    interval_cases mB <;> simp at hBm <;> omega
  set Q := 2 ^ k with hQ
  have hB4 : B = 4 * Q := by rw [hBm, pow_add]; ring
  have hQ16 : 16 ≤ Q := by omega
  have hk : 1 ≤ k := by
    by_contra h; have : k = 0 := by omega
    rw [this] at hQ; simp at hQ; omega
  have hδB : δ < B := by omega
  have hδ2 : δ ^ 2 < B ^ 2 := Nat.pow_lt_pow_left hδB two_ne_zero
  obtain ⟨d0, d1, d2, hd0, hd1, hd2, h1⟩ := test1
  have hd2z : d2 = 0 := by
    by_contra h
    have : B ^ 2 ≤ d2 * B ^ 2 := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h1' : δ ^ 2 = d0 + d1 * B := by rw [hd2z] at h1; simpa using h1
  -- `d0 ∈ {0, 1}`
  have hd0' : d0 = δ ^ 2 % 4 := by
    rw [h1', hB4, show d0 + d1 * (4 * Q) = d0 + d1 * Q * 4 by ring, Nat.add_mul_mod_self_right,
      Nat.mod_eq_of_lt (by omega)]
  rcases sq_mod_four δ with h4 | h4
  · -- `d0 = 0`: `δ² = d1 B`, so `B ≤ δ² ≤ x²`
    rw [h4] at hd0'
    subst hd0'
    rw [zero_add] at h1'
    have hd1pos : 1 ≤ d1 := by
      by_contra h
      have : d1 = 0 := by omega
      rw [this, zero_mul] at h1'
      have : δ = 0 := by simpa using h1'
      omega
    have hBδ : B ≤ δ ^ 2 := by rw [h1']; exact Nat.le_mul_of_pos_left _ hd1pos
    have hδx2 : δ ^ 2 ≤ x ^ 2 := Nat.pow_le_pow_left hδx 2
    have hx2 : x ^ 2 < B ^ 2 := Nat.pow_lt_pow_left hxB two_ne_zero
    have hh5ge : 5 ≤ 5 * x ^ 2 / B := by
      rw [Nat.le_div_iff_mul_le (by omega)]; linarith
    have hh5lt : 5 * x ^ 2 / B < 5 * B := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; nlinarith
    have hh7lt : 7 * x ^ 2 / B < 7 * B := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]; nlinarith
    obtain ⟨hr5, hm5⟩ := padded_test hB hd1 (by norm_num) h1' hh5lt test5
    obtain ⟨hr7, hm7⟩ := padded_test hB hd1 (by norm_num) h1' hh7lt test7
    -- `7 h5 < 5 h7 + 5` and `5 h7 < 7 h5 + 7`
    have hx5 := Nat.div_add_mod (5 * x ^ 2) B
    have hx7 := Nat.div_add_mod (7 * x ^ 2) B
    have hm5' := Nat.mod_lt (5 * x ^ 2) (show 0 < B by omega)
    have hm7' := Nat.mod_lt (7 * x ^ 2) (show 0 < B by omega)
    have h35 : 7 * (B * (5 * x ^ 2 / B) + 5 * x ^ 2 % B) =
        5 * (B * (7 * x ^ 2 / B) + 7 * x ^ 2 % B) := by rw [hx5, hx7]; ring
    have hA : 7 * (5 * x ^ 2 / B) < 5 * (7 * x ^ 2 / B) + 5 := by
      have : B * (7 * (5 * x ^ 2 / B)) < B * (5 * (7 * x ^ 2 / B) + 5) := by
        linarith only [h35, hm7', Nat.zero_le (5 * x ^ 2 % B)]
      exact Nat.lt_of_mul_lt_mul_left this
    have hB' : 5 * (7 * x ^ 2 / B) < 7 * (5 * x ^ 2 / B) + 7 := by
      have : B * (5 * (7 * x ^ 2 / B)) < B * (7 * (5 * x ^ 2 / B) + 7) := by
        linarith only [h35, hm5', Nat.zero_le (7 * x ^ 2 % B)]
      exact Nat.lt_of_mul_lt_mul_left this
    exact (carry_contra hB (Nat.div_add_mod (5 * x ^ 2 / B) B).symm
      (Nat.div_add_mod (7 * x ^ 2 / B) B).symm hr5 hr7 (by omega) (by omega) hh5ge hA hB').elim
  · -- `d0 = 1`: `δ² = 1 + d1 B`, `δ < Q`, and `δ² ≡ 1 (mod Q)`
    rw [h4] at hd0'
    subst hd0'
    have hδQ : δ < Q := by
      by_contra h
      push Not at h
      have h1 : Q * Q ≤ δ * δ := Nat.mul_le_mul h h
      have h2 : 16 * Q ≤ Q * Q := Nat.mul_le_mul_right Q hQ16
      have h3 : d1 * B ≤ 3 * B := Nat.mul_le_mul_right _ hd1
      nlinarith
    have h1'' : δ ^ 2 = 1 + 4 * (d1 * 2 ^ k) := by rw [h1', hB4]; ring
    exact sqrt_one_mod_pow_two hk hδ hδQ h1''

end Jones1980
