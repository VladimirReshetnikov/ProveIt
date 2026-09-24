import Diophantine.Paper1976.Theorem39
import Diophantine.Paper1976.Factorial

/-!
# JSWW 1976, §3: Theorem 3.9, the Case 1 congruence and the estimates for `β`

This file proves the two analytic cores of the proof of Theorem 3.9:

* `case1_congruence` ((12)–(15), (19)): if `0 < σ − (w+1)x < x` then
  `|σ − (w+1)x − C(n,k)| < 1/4`;
* `beta_estimate` ((16)–(21)): with `C, L, R` the Pell numbers of the proof and
  `|s − C(n,k)| < 1/4`, the number `β = R/(s (1 − R/C)² L)` satisfies `|β − k!| < 1/2`.

Together with the size bounds (2)–(5) and the estimate (11) from `Theorem39.lean`,
these give both directions of Theorem 3.9 (`Theorem39c.lean`).
-/

namespace JSWW1976

open Pell Diophantine Finset

/-! ### Natural-number side conditions -/

/-- `n ≤ C(n,k)` for `1 ≤ k < n`. -/
theorem le_choose_of_lt {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) : n ≤ n.choose k := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  induction n with
  | zero => omega
  | succ n ih =>
    rcases Nat.lt_or_ge (k' + 1) n with h | h
    · rw [Nat.choose_succ_succ']
      have h1 := ih h
      have h2 : 0 < n.choose k' := Nat.choose_pos (by omega)
      omega
    · have : k' + 1 = n := by omega
      subst this
      rw [Nat.choose_succ_self_right]

/-- `k! ≤ k^(k-1)` for `k ≥ 1`. -/
theorem factorial_le_pow_pred {k : ℕ} (hk : 1 ≤ k) : k.factorial ≤ k ^ (k - 1) := by
  induction k, hk using Nat.le_induction with
  | base => norm_num
  | succ k hk ih =>
    rw [Nat.factorial_succ, Nat.add_sub_cancel]
    have h1 : k ^ (k - 1) ≤ (k + 1) ^ (k - 1) := Nat.pow_le_pow_left (by omega) _
    calc (k + 1) * k.factorial ≤ (k + 1) * (k + 1) ^ (k - 1) := Nat.mul_le_mul_left _ (ih.trans h1)
      _ = (k + 1) ^ (k - 1 + 1) := by ring
      _ = (k + 1) ^ k := by rw [Nat.sub_add_cancel hk]

/-- `k^k < (2k)^(2k)` for `k ≥ 1`. -/
theorem pow_self_lt {k : ℕ} (hk : 1 ≤ k) : k ^ k < (2 * k) ^ (2 * k) := by
  calc k ^ k < (2 * k) ^ k := Nat.pow_lt_pow_left (by omega) (by omega)
    _ ≤ (2 * k) ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)

/-- `k + 3 ≤ n` when `(2k)^(2k) < n`, `k ≥ 1`. -/
theorem add_three_le {k n : ℕ} (hk : 1 ≤ k) (hn : (2 * k) ^ (2 * k) < n) : k + 3 ≤ n := by
  have : 4 * k * k ≤ (2 * k) ^ (2 * k) := by
    calc 4 * k * k = (2 * k) ^ 2 := by ring
      _ ≤ (2 * k) ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

/-- (i): `5 · k! ≤ C(n,k)` when `(2k)^(2k) < n`, `k ≥ 1`. -/
theorem five_factorial_le_choose {k n : ℕ} (hk : 1 ≤ k) (hn : (2 * k) ^ (2 * k) < n) :
    5 * k.factorial ≤ n.choose k := by
  have hkn : k < n := by have := add_three_le hk hn; omega
  have hdesc : k.factorial * n.choose k = n.descFactorial k :=
    (Nat.descFactorial_eq_factorial_mul_choose n k).symm
  -- n ≤ descFactorial n k
  have hn_le : n ≤ n.descFactorial k := by
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    rw [Nat.succ_descFactorial_succ]
    exact Nat.le_mul_of_pos_right _ (Nat.descFactorial_pos.2 (by omega))
  -- 5 (k!)² ≤ n
  have h5 : 5 * (k.factorial * k.factorial) ≤ n := by
    rcases Nat.eq_or_lt_of_le hk with rfl | hk2
    · simp; omega
    · have hf : k.factorial ≤ k ^ k :=
        (factorial_le_pow_pred hk).trans (Nat.pow_le_pow_right (by omega) (by omega))
      have h4 : 5 ≤ 2 ^ k * 2 ^ k := by
        have : 4 ≤ 2 ^ k := by
          calc 4 = 2 ^ 2 := by norm_num
            _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
        nlinarith
      have e : (2 * k) ^ (2 * k) = (2 ^ k * 2 ^ k) * (k ^ k * k ^ k) := by ring
      calc 5 * (k.factorial * k.factorial) ≤ (2 ^ k * 2 ^ k) * (k ^ k * k ^ k) :=
            Nat.mul_le_mul h4 (Nat.mul_le_mul hf hf)
        _ = (2 * k) ^ (2 * k) := e.symm
        _ ≤ n := hn.le
  -- 5 k! · k! ≤ n ≤ desc = k! C
  have : k.factorial * (5 * k.factorial) ≤ k.factorial * n.choose k := by
    rw [hdesc]
    calc k.factorial * (5 * k.factorial) = 5 * (k.factorial * k.factorial) := by ring
      _ ≤ n := h5
      _ ≤ n.descFactorial k := hn_le
  exact Nat.le_of_mul_le_mul_left this (Nat.factorial_pos k)

/-- (iv): `20 · k! · (k−1)² ≤ n` when `(2k)^(2k) < n`, `k ≥ 1`. -/
theorem twenty_factorial_le {k n : ℕ} (hk : 1 ≤ k) (hn : (2 * k) ^ (2 * k) < n) :
    20 * k.factorial * (k - 1) ^ 2 ≤ n := by
  rcases Nat.eq_or_lt_of_le hk with rfl | hk2
  · simp
  · have hf : k.factorial ≤ k ^ (k - 1) := factorial_le_pow_pred hk
    have hsq : (k - 1) ^ 2 ≤ k ^ 2 := Nat.pow_le_pow_left (by omega) _
    -- 20 k^(k-1) k^2 = 20 k^(k+1) ≤ 4^k k^(k-1) k^(k+1) = (2k)^(2k)
    have h20 : 20 ≤ 2 ^ k * 2 ^ k * k ^ (k - 1) := by
      have h1 : 4 ≤ 2 ^ k := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
      have h2 : 2 ≤ k ^ (k - 1) := by
        calc 2 ≤ k := hk2
          _ = k ^ 1 := (pow_one k).symm
          _ ≤ k ^ (k - 1) := Nat.pow_le_pow_right (by omega) (by omega)
      nlinarith
    have hkk : k ^ (2 * k) = k ^ (k - 1) * (k ^ (k - 1) * k ^ 2) := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have e : (2 * k) ^ (2 * k) = 2 ^ k * 2 ^ k * k ^ (k - 1) * (k ^ (k - 1) * k ^ 2) := by
      rw [mul_pow, hkk, ← pow_add, two_mul]
      ring
    calc 20 * k.factorial * (k - 1) ^ 2 ≤ 20 * k ^ (k - 1) * k ^ 2 := by
          apply Nat.mul_le_mul (Nat.mul_le_mul_left _ hf) hsq
      _ = 20 * (k ^ (k - 1) * k ^ 2) := by ring
      _ ≤ 2 ^ k * 2 ^ k * k ^ (k - 1) * (k ^ (k - 1) * k ^ 2) := Nat.mul_le_mul_right _ h20
      _ = (2 * k) ^ (2 * k) := e.symm
      _ ≤ n := hn.le

/-- `k · k! ≤ k^k ≤ n` when `(2k)^(2k) < n`, `k ≥ 1`. -/
theorem mul_factorial_le {k n : ℕ} (hk : 1 ≤ k) (hn : (2 * k) ^ (2 * k) < n) :
    k * k.factorial ≤ n := by
  have hf : k.factorial ≤ k ^ (k - 1) := factorial_le_pow_pred hk
  calc k * k.factorial ≤ k * k ^ (k - 1) := Nat.mul_le_mul_left _ hf
    _ = k ^ k := by rw [← pow_succ', Nat.sub_add_cancel hk]
    _ ≤ n := (pow_self_lt hk).le.trans hn.le

/-- `k! C(n,k) ≤ n^k`. -/
theorem factorial_mul_choose_le (n k : ℕ) : k.factorial * n.choose k ≤ n ^ k := by
  rw [← Nat.descFactorial_eq_factorial_mul_choose]
  exact Nat.descFactorial_le_pow n k

/-! ### Case 1: the congruence (12)–(15) and the estimate (19) -/

/-- If `0 < σ − (w+1)x < x` (Case 1 of the proof), then `|σ − (w+1)x − C(n,k)| < 1/4`. -/
theorem case1_congruence {k n x w M : ℕ} {σ : ℝ} (hk : 1 ≤ k) (hkn : k < n) (hn5 : 5 ≤ n)
    (hx8 : 8 * n ^ k < x) (hx2 : 8 * 2 ^ n < x) (hM : M = 16 * n * x * (w + 2) + 1)
    (hσa : |σ - ((x : ℝ) + 1) ^ n / (x : ℝ) ^ k| ≤ (n : ℝ) / M * (((x : ℝ) + 1) ^ n / (x : ℝ) ^ k))
    (hσ2 : ((x : ℝ) + 1) ^ n / (x : ℝ) ^ k / 2 < σ)
    (hs0 : 0 < σ - (w + 1) * x) (hsx : σ - (w + 1) * x < x) :
    |σ - (w + 1) * x - n.choose k| < 1 / 4 := by
  obtain ⟨w', hw'1, hfloor, hfrac⟩ := lemma_3_3 hkn hx2
  set a : ℝ := ((x : ℝ) + 1) ^ n / (x : ℝ) ^ k with ha_def
  have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hxR : (0 : ℝ) < x := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hMR : (M : ℝ) = 16 * n * x * (w + 2) + 1 := by rw [hM]; push_cast; ring
  have hM0 : (0 : ℝ) < M := by rw [hMR]; positivity
  have ha0 : 0 < a := by positivity
  -- ⌊a⌋ = C(n,k) + w' x ≤ a < ⌊a⌋ + 1/8
  have hT : (((n.choose k + w' * x : ℕ) : ℤ) : ℝ) = (n.choose k : ℝ) + w' * x := by
    push_cast; ring
  have hfl : (n.choose k : ℝ) + w' * x ≤ a := by
    have := Int.floor_le a
    rw [hfloor, hT] at this
    exact this
  have hfr : a - ((n.choose k : ℝ) + w' * x) < 1 / 8 := by
    have := hfrac
    push_cast at this
    exact this
  -- ε₁ = |σ − a| < 1/8
  have hσw : σ < (w + 2) * x := by linarith
  have hε : (n : ℝ) / M * a < 1 / 8 := by
    have h1 : (n : ℝ) * a < n * (2 * σ) := mul_lt_mul_of_pos_left (by linarith) hnR
    have h2 : 16 * (n : ℝ) * σ < 16 * n * ((w + 2) * x) :=
      mul_lt_mul_of_pos_left hσw (by positivity)
    have h3 : 16 * (n : ℝ) * σ < M := by rw [hMR]; linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM0]
    linarith
  have hsub : |σ - a| < 1 / 8 := lt_of_le_of_lt hσa hε
  rw [abs_lt] at hsub
  -- 5 ≤ C(n,k) and 8 C(n,k) < x
  have hC5 : (5 : ℝ) ≤ n.choose k := by
    have := le_choose_of_lt hk hkn; exact_mod_cast (show 5 ≤ n.choose k by omega)
  have hCx : (n.choose k : ℝ) * 8 < x := by
    have h1 := choose_le_pow' n k
    exact_mod_cast (show n.choose k * 8 < x by nlinarith)
  -- σ − (w+1)x = C(n,k) + d·x + δ with d = w' − w − 1 an integer and |δ| small
  have key : σ - (w + 1) * x
      = n.choose k + ((w' : ℝ) - w - 1) * x + ((a - (n.choose k + w' * x)) + (σ - a)) := by
    ring
  have hd : ((w' : ℝ) - w - 1) = 0 := by
    rcases Nat.lt_trichotomy w' (w + 1) with h | h | h
    · exfalso
      have h1 : (w' : ℝ) ≤ w := by exact_mod_cast (show w' ≤ w by omega)
      have h2 : ((w' : ℝ) - w - 1) * x ≤ -x := by nlinarith
      linarith
    · rw [h]; push_cast; ring
    · exfalso
      have h1 : (w : ℝ) + 2 ≤ w' := by exact_mod_cast (show w + 2 ≤ w' by omega)
      have h2 : x ≤ ((w' : ℝ) - w - 1) * x := by nlinarith
      linarith
  rw [hd, zero_mul, add_zero] at key
  rw [abs_lt]
  constructor <;> linarith

/-! ### The estimates (16)–(21) for `β` -/

/-- The upper estimate (20), in abstract form.  Here `y = 2Mx`, `r ≤ n^k y^k`, `l ≥ (y−1)^k`,
`s ≥ C(n,k) − 1/4`, `r/c < 1/y²`, and the side conditions (i)–(iv). -/
theorem beta_upper {k n : ℕ} {r c l s y : ℝ} (hk : 1 ≤ k) (hn : (2 * k) ^ (2 * k) < n)
    (hy : 4 ≤ y) (hyk : 2 * k < y) (hy10 : 10 * k * k.factorial ≤ y / 2)
    (hr : r ≤ (n : ℝ) ^ k * y ^ k) (hr0 : 0 < r) (hc0 : 0 < c) (hl : (y - 1) ^ k ≤ l)
    (hs : (n.choose k : ℝ) - 1 / 4 ≤ s) (hρ : r / c < 1 / y ^ 2) :
    r / (s * (1 - r / c) ^ 2 * l) ≤ (k.factorial : ℝ) * (1 + 1 / (10 * k.factorial)) ^ 4 := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hkf1 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hkf0 : (0 : ℝ) < k.factorial := by linarith
  have hC5 : (5 : ℝ) * k.factorial ≤ n.choose k := by exact_mod_cast five_factorial_le_choose hk hn
  have hC0 : (0 : ℝ) < n.choose k := by linarith
  have h20 : (20 : ℝ) * k.factorial * ((k : ℝ) - 1) ^ 2 ≤ n := by
    have := twenty_factorial_le hk hn
    have h' : ((20 * k.factorial * (k - 1) ^ 2 : ℕ) : ℝ) ≤ n := by exact_mod_cast this
    push_cast [Nat.cast_sub hk] at h'
    exact h'
  have hn2 : 2 * (k - 1) ^ 2 < n := by
    have h4 : 4 * (k * k) ≤ (2 * k) ^ (2 * k) := by
      calc 4 * (k * k) = (2 * k) ^ 2 := by ring
        _ ≤ (2 * k) ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    have : (k - 1) ^ 2 ≤ k * k := by
      have : k - 1 ≤ k := Nat.sub_le k 1
      calc (k - 1) ^ 2 = (k - 1) * (k - 1) := by ring
        _ ≤ k * k := Nat.mul_le_mul this this
    omega
  -- the factors
  set t : ℝ := 1 / y ^ 2 with ht
  have hy0 : 0 < y := by linarith
  have hy1 : 0 < y - 1 := by linarith
  have ht0 : 0 ≤ t := by positivity
  have ht_le : t ≤ 1 / 16 := by
    rw [ht]; apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hρ0 : 0 ≤ r / c := by positivity
  have h1ρ : 1 - t ≤ 1 - r / c := by linarith
  have h1t : 0 < 1 - t := by linarith
  have hs0 : 0 < s := by linarith
  have hl0 : 0 < l := lt_of_lt_of_le (pow_pos hy1 k) hl
  set C : ℝ := (n.choose k : ℝ) with hCdef
  -- β ≤ (n^k y^k) / ((C − 1/4) (1−t)² (y−1)^k)
  have hden : (C - 1 / 4) * (1 - t) ^ 2 * (y - 1) ^ k ≤ s * (1 - r / c) ^ 2 * l := by
    apply mul_le_mul
    · apply mul_le_mul hs (pow_le_pow_left₀ h1t.le h1ρ 2) (sq_nonneg _) hs0.le
    · exact hl
    · exact pow_nonneg hy1.le k
    · exact mul_nonneg hs0.le (sq_nonneg _)
  have hstep1 : r / (s * (1 - r / c) ^ 2 * l)
      ≤ (n : ℝ) ^ k * y ^ k / ((C - 1 / 4) * (1 - t) ^ 2 * (y - 1) ^ k) :=
    div_le_div₀ (mul_nonneg (by positivity) (pow_nonneg hy0.le k)) hr
      (mul_pos (mul_pos (by linarith) (pow_pos h1t 2)) (pow_pos hy1 k)) hden
  -- factor the bound
  have hC4 : C - 1 / 4 = C * (1 - 1 / (4 * C)) := by field_simp
  have h1C : 0 < 1 - 1 / (4 * C) := by
    have : 1 / (4 * C) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    linarith
  have hfac : (n : ℝ) ^ k * y ^ k / ((C - 1 / 4) * (1 - t) ^ 2 * (y - 1) ^ k)
      = ((n : ℝ) ^ k / C) * (y / (y - 1)) ^ k * (1 - 1 / (4 * C))⁻¹ * ((1 - t)⁻¹) ^ 2 := by
    rw [hC4, div_pow]
    field_simp
    try ring
  rw [hfac] at hstep1
  -- bound each factor by (1 + ε), the first by k! (1 + ε), with ε = 1/(10 k!)
  set ε : ℝ := 1 / (10 * k.factorial) with hε
  have hε0 : 0 < ε := by positivity
  have hF1 : (n : ℝ) ^ k / C ≤ k.factorial * (1 + ε) := by
    have h34 := lemma_3_4 hk hn2
    have : 2 * ((k : ℝ) - 1) ^ 2 / n ≤ ε := by
      rw [hε, div_le_div_iff₀ hnR (by positivity)]
      linarith only [h20]
    calc (n : ℝ) ^ k / C ≤ k.factorial * (1 + 2 * ((k : ℝ) - 1) ^ 2 / n) := h34
      _ ≤ k.factorial * (1 + ε) := by
          apply mul_le_mul_of_nonneg_left _ hkf0.le; linarith only [this]
  have hF2 : (y / (y - 1)) ^ k ≤ 1 + ε := by
    have h31 := lemma_3_1 hk (β := y) (by linarith)
    have h20y : 20 * (k : ℝ) * k.factorial ≤ y := by linarith only [hy10]
    have : 2 * (k : ℝ) / y ≤ ε := by
      rw [hε, div_le_div_iff₀ hy0 (by positivity)]
      nlinarith only [h20y]
    linarith only [h31, this]
  have hF3 : (1 - 1 / (4 * C))⁻¹ ≤ 1 + ε := by
    have hα0 : 0 ≤ 1 / (4 * C) := by positivity
    have hα1 : 1 / (4 * C) ≤ 1 / 2 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    have h28 := lemma_2_8 hα0 hα1
    have h2 : 2 * (1 / (4 * C)) ≤ ε := by
      rw [hε]
      have : 2 * (1 / (4 * C)) = 1 / (2 * C) := by field_simp; ring
      rw [this]
      apply one_div_le_one_div_of_le (by positivity); linarith only [hC5]
    linarith only [h28, h2]
  have hF4 : ((1 - t)⁻¹) ^ 2 ≤ 1 + ε := by
    have h28 := lemma_2_8 ht0 (by linarith only [ht_le])
    have h1 : ((1 - t)⁻¹) ^ 2 ≤ (1 + 2 * t) ^ 2 := pow_le_pow_left₀ (by positivity) h28 2
    have h2 : (1 + 2 * t) ^ 2 ≤ 1 + 8 * t := by nlinarith only [ht0, ht_le]
    have h3 : 8 * t ≤ ε := by
      rw [ht, hε]
      have h20y : 20 * (k : ℝ) * k.factorial ≤ y := by linarith only [hy10]
      have : (8 : ℝ) * (1 / y ^ 2) = 8 / y ^ 2 := by ring
      rw [this, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [h20y, hy, hkR, hkf1]
    linarith only [h1, h2, h3]
  -- combine
  have hnn1 : 0 ≤ (n : ℝ) ^ k / C := by positivity
  have hnn2 : 0 ≤ (y / (y - 1)) ^ k := pow_nonneg (div_nonneg hy0.le hy1.le) k
  have hnn3 : 0 ≤ (1 - 1 / (4 * C))⁻¹ := inv_nonneg.2 h1C.le
  have hnn4 : 0 ≤ ((1 - t)⁻¹) ^ 2 := sq_nonneg _
  have hprod : (n : ℝ) ^ k / C * (y / (y - 1)) ^ k * (1 - 1 / (4 * C))⁻¹ * ((1 - t)⁻¹) ^ 2
      ≤ k.factorial * (1 + ε) * (1 + ε) * (1 + ε) * (1 + ε) := by
    have hA : (n : ℝ) ^ k / C * (y / (y - 1)) ^ k ≤ k.factorial * (1 + ε) * (1 + ε) :=
      mul_le_mul hF1 hF2 hnn2 (by positivity)
    have hB : (n : ℝ) ^ k / C * (y / (y - 1)) ^ k * (1 - 1 / (4 * C))⁻¹
        ≤ k.factorial * (1 + ε) * (1 + ε) * (1 + ε) :=
      mul_le_mul hA hF3 hnn3 (by positivity)
    exact mul_le_mul hB hF4 hnn4 (by positivity)
  calc r / (s * (1 - r / c) ^ 2 * l) ≤ _ := hstep1
    _ ≤ k.factorial * (1 + ε) * (1 + ε) * (1 + ε) * (1 + ε) := hprod
    _ = k.factorial * (1 + ε) ^ 4 := by ring

/-- The lower estimate (21), in abstract form.  Here `y = 2Mx`, `n y = 2Mnx`,
`r ≥ (ny−1)^k`, `l ≤ y^k`, `s ≤ C(n,k) + 1/4`, `0 ≤ r/c < 1`. -/
theorem beta_lower {k n : ℕ} {r c l s y : ℝ} (hk : 1 ≤ k) (hn : (2 * k) ^ (2 * k) < n)
    (hy : 4 ≤ y) (hz4 : 4 * (k : ℝ) * k.factorial ≤ n * y)
    (hr : ((n : ℝ) * y - 1) ^ k ≤ r) (hc0 : 0 < c) (hl0 : 0 < l) (hl : l ≤ y ^ k)
    (hs : s ≤ (n.choose k : ℝ) + 1 / 4) (hs0 : 0 < s) (hρ0 : 0 ≤ r / c) (hρ1 : r / c < 1) :
    (k.factorial : ℝ) * (1 - 1 / (4 * k.factorial)) ^ 2 ≤ r / (s * (1 - r / c) ^ 2 * l) := by
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hnR : (5 : ℝ) ≤ n := by
    have := add_three_le hk hn
    have h4 : 4 ≤ (2 * k) ^ (2 * k) := by
      calc 4 = (2 * 1) ^ (2 * 1) := by norm_num
        _ ≤ (2 * k) ^ (2 * 1) := Nat.pow_le_pow_left (by omega) _
        _ ≤ (2 * k) ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    exact_mod_cast (show 5 ≤ n by omega)
  have hkf1 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hkf0 : (0 : ℝ) < k.factorial := by linarith
  have hC5 : (5 : ℝ) * k.factorial ≤ n.choose k := by exact_mod_cast five_factorial_le_choose hk hn
  have hkfC : (k.factorial : ℝ) * n.choose k ≤ (n : ℝ) ^ k := by
    exact_mod_cast factorial_mul_choose_le n k
  set C : ℝ := (n.choose k : ℝ) with hCdef
  have hC0 : (0 : ℝ) < C := by linarith
  have hy0 : 0 < y := by linarith
  have hny : 0 < (n : ℝ) * y := by positivity
  have hz1 : 0 < (n : ℝ) * y - 1 := by nlinarith
  have hr0 : 0 < r := lt_of_lt_of_le (pow_pos hz1 k) hr
  -- the denominator is at most (C + 1/4) y^k
  have hden : s * (1 - r / c) ^ 2 * l ≤ (C + 1 / 4) * y ^ k := by
    have h1 : (1 - r / c) ^ 2 ≤ 1 := by nlinarith only [hρ0, hρ1]
    calc s * (1 - r / c) ^ 2 * l ≤ s * 1 * l := by
          apply mul_le_mul_of_nonneg_right _ hl0.le
          exact mul_le_mul_of_nonneg_left h1 hs0.le
      _ = s * l := by ring
      _ ≤ (C + 1 / 4) * y ^ k := mul_le_mul hs hl hl0.le (by linarith)
  have h1ρ : 0 < 1 - r / c := by linarith
  have hden0 : 0 < s * (1 - r / c) ^ 2 * l := by positivity
  have hstep1 : ((n : ℝ) * y - 1) ^ k / ((C + 1 / 4) * y ^ k)
      ≤ r / (s * (1 - r / c) ^ 2 * l) :=
    div_le_div₀ hr0.le hr hden0 hden
  -- factor the bound
  have hfac : ((n : ℝ) * y - 1) ^ k / ((C + 1 / 4) * y ^ k)
      = ((n : ℝ) ^ k / C) * (1 - 1 / ((n : ℝ) * y)) ^ k * (1 + 1 / (4 * C))⁻¹ := by
    have e1 : ((n : ℝ) * y - 1) ^ k = (n : ℝ) ^ k * y ^ k * (1 - 1 / ((n : ℝ) * y)) ^ k := by
      rw [← mul_pow, ← mul_pow]
      congr 1
      field_simp
    have e2 : C + 1 / 4 = C * (1 + 1 / (4 * C)) := by field_simp
    rw [e1, e2]
    field_simp
    try ring
  rw [hfac] at hstep1
  -- bound each factor from below
  have hF1 : (k.factorial : ℝ) ≤ (n : ℝ) ^ k / C := by
    rw [le_div_iff₀ hC0]; exact hkfC
  have h1ny : 0 ≤ 1 - 1 / ((n : ℝ) * y) := by
    rw [sub_nonneg, div_le_one hny]; linarith
  have hF2 : 1 - 1 / (4 * (k.factorial : ℝ)) ≤ (1 - 1 / ((n : ℝ) * y)) ^ k := by
    have h27 := lemma_2_7 (α := 1 / ((n : ℝ) * y)) (by rw [div_le_one hny]; linarith) k
    have : (k : ℝ) * (1 / ((n : ℝ) * y)) ≤ 1 / (4 * k.factorial) := by
      rw [mul_one_div, div_le_div_iff₀ hny (by positivity)]
      linarith only [hz4]
    linarith only [h27, this]
  have hF3 : 1 - 1 / (4 * (k.factorial : ℝ)) ≤ (1 + 1 / (4 * C))⁻¹ := by
    have hu : 0 ≤ 1 / (4 * C) := by positivity
    have h1 : 1 - 1 / (4 * C) ≤ (1 + 1 / (4 * C))⁻¹ := by
      rw [inv_eq_one_div, le_div_iff₀ (by positivity)]
      nlinarith only [hu]
    have h2 : 1 / (4 * C) ≤ 1 / (4 * (k.factorial : ℝ)) := by
      apply one_div_le_one_div_of_le (by positivity); linarith only [hC5, hkf1]
    linarith only [h1, h2]
  have hq0 : 0 ≤ 1 - 1 / (4 * (k.factorial : ℝ)) := by
    have : 1 / (4 * (k.factorial : ℝ)) ≤ 1 / 4 := by
      apply one_div_le_one_div_of_le (by norm_num); linarith
    linarith
  calc (k.factorial : ℝ) * (1 - 1 / (4 * k.factorial)) ^ 2
      = k.factorial * (1 - 1 / (4 * k.factorial)) * (1 - 1 / (4 * k.factorial)) := by ring
    _ ≤ (n : ℝ) ^ k / C * (1 - 1 / ((n : ℝ) * y)) ^ k * (1 + 1 / (4 * C))⁻¹ := by
        apply mul_le_mul (mul_le_mul hF1 hF2 hq0 (by positivity)) hF3 hq0
        exact mul_nonneg (by positivity) (pow_nonneg h1ny k)
    _ ≤ _ := hstep1

end JSWW1976
