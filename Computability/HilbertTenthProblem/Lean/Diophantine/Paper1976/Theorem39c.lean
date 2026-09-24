import Diophantine.Paper1976.Theorem39b

/-!
# JSWW 1976, §3: Theorem 3.9, the remaining estimates of the proof

* `rho_bound` (17): `R/C < 1/(2Mx)²`;
* `sigma_small`: if `p' ≥ 1` or `l' ≥ 1` then `σ < 1/2` (so `β ≤ 0`, contradicting (XIV));
* `beta_lt_half_of_large_R`: if `r' ≥ 1` (so `R > C³`) then `β < 1/2`;
* `case2_bound`: in Case 2 (`σ − (w+1)x ≥ x`), `β < 1/2`;
* `beta_estimate`: the packaged conclusion `|β − k!| < 1/2` of (20)–(21) for the Pell numbers
  `C = ψ_{M(x+1)}(n+1)`, `L = ψ_{Mx}(k+1)`, `R = ψ_{Mnx}(k+1)`.
-/

namespace JSWW1976

open Pell Diophantine

/-- (17): `r/c < 1/y²` when `r ≤ n^k y^k`, `c ≥ y^n`, `n^k < y` and `k + 3 ≤ n`. -/
theorem rho_bound {k n : ℕ} {r c y : ℝ} (hkn : k + 3 ≤ n) (hy : 1 < y) (hnk : (n : ℝ) ^ k < y)
    (hr : r ≤ (n : ℝ) ^ k * y ^ k) (hc : y ^ n ≤ c) (hc0 : 0 < c) (hr0 : 0 ≤ r) :
    r / c < 1 / y ^ 2 := by
  have hy0 : 0 < y := by linarith
  have h2 : y ^ n = y ^ k * y ^ 3 * y ^ (n - k - 3) := by
    rw [← pow_add, ← pow_add]; congr 1; omega
  have hge1 : (1 : ℝ) ≤ y ^ (n - k - 3) := one_le_pow₀ hy.le
  rw [div_lt_div_iff₀ hc0 (by positivity), one_mul]
  have hyk : 0 < y ^ k := pow_pos hy0 k
  calc r * y ^ 2 ≤ (n : ℝ) ^ k * y ^ k * y ^ 2 := by
        apply mul_le_mul_of_nonneg_right hr (by positivity)
    _ < y * y ^ k * y ^ 2 := by
        apply mul_lt_mul_of_pos_right (mul_lt_mul_of_pos_right hnk hyk) (by positivity)
    _ = y ^ k * y ^ 3 := by ring
    _ ≤ y ^ k * y ^ 3 * y ^ (n - k - 3) := by
        apply le_mul_of_one_le_right (by positivity) hge1
    _ = y ^ n := h2.symm
    _ ≤ c := hc

/-- If `K L ≥ (2M−1)^(n+M−1)` (which happens when `p' ≥ 1` or `l' ≥ 1`) then
`σ = C/(KL) < 1/2`. -/
theorem sigma_small {n x M : ℕ} {KL C : ℝ} (hM : 2 * n + 2 ≤ M) (hMx : x + 1 ≤ 2 * M - 1)
    (hKL : ((2 * M - 1 : ℕ) : ℝ) ^ (n + M - 1) ≤ KL) (hKL0 : 0 < KL)
    (hC : C ≤ (2 * (M * (x + 1)) : ℝ) ^ n) (hC0 : 0 ≤ C) : C / KL < 1 / 2 := by
  have hM2 : 2 ≤ M := by omega
  have hcM : ((2 * M - 1 : ℕ) : ℝ) = 2 * M - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcM] at hKL
  have hMR : (2 : ℝ) ≤ M := by exact_mod_cast hM2
  have hxR : (x : ℝ) + 1 ≤ 2 * M - 1 := by
    have : ((x + 1 : ℕ) : ℝ) ≤ ((2 * M - 1 : ℕ) : ℝ) := by exact_mod_cast hMx
    rw [hcM] at this; push_cast at this; exact this
  have h2M1 : (2 : ℝ) < 2 * M - 1 := by linarith
  -- (2M−1)^(n+M−1) = ((2M−1)²)^n (2M−1)^(M−n−1) ≥ (2M)^n · 2 (x+1)^n
  have e : (2 * (M : ℝ) - 1) ^ (n + M - 1)
      = ((2 * M - 1) ^ 2) ^ n * ((2 * M - 1) ^ n * (2 * M - 1)) * (2 * M - 1) ^ (M - 2 * n - 2) := by
    rw [← pow_mul, ← pow_succ, ← pow_add, ← pow_add]; congr 1; omega
  have h1 : (2 * (M : ℝ)) ^ n ≤ ((2 * M - 1) ^ 2) ^ n := by
    apply pow_le_pow_left₀ (by positivity); nlinarith
  have h2 : ((x : ℝ) + 1) ^ n ≤ (2 * M - 1) ^ n := pow_le_pow_left₀ (by positivity) hxR n
  have h3 : (1 : ℝ) ≤ (2 * M - 1) ^ (M - 2 * n - 2) := one_le_pow₀ (by linarith)
  have hbig : 2 * (2 * (M * (x + 1)) : ℝ) ^ n < (2 * M - 1) ^ (n + M - 1) := by
    rw [e]
    have hx0 : (0 : ℝ) < ((x : ℝ) + 1) ^ n := by positivity
    have e2 : (2 * (M * (x + 1)) : ℝ) ^ n = (2 * M) ^ n * (x + 1) ^ n := by rw [← mul_pow]; ring_nf
    rw [e2]
    calc 2 * ((2 * (M : ℝ)) ^ n * (x + 1) ^ n) = (2 * M) ^ n * ((x + 1) ^ n * 2) := by ring
      _ < ((2 * M - 1) ^ 2) ^ n * ((2 * M - 1) ^ n * (2 * M - 1)) := by
          apply mul_lt_mul' h1 _ (by positivity) (by positivity)
          apply mul_lt_mul' h2 h2M1 (by norm_num) (by positivity)
      _ ≤ ((2 * M - 1) ^ 2) ^ n * ((2 * M - 1) ^ n * (2 * M - 1)) * (2 * M - 1) ^ (M - 2 * n - 2) := by
          apply le_mul_of_one_le_right (by positivity) h3
  rw [div_lt_iff₀ hKL0]
  linarith

/-- If `R > C³` (which happens when `r' ≥ 1`) then `β < 1/2`, given `s > 1/2`, `L ≥ 1`, `C ≥ 5`. -/
theorem beta_lt_half_of_large_R {R C L s : ℝ} (hC : 5 ≤ C) (hR : C ^ 3 < R) (hs : 1 / 2 < s)
    (hL : 1 ≤ L) : R / (s * (1 - R / C) ^ 2 * L) < 1 / 2 := by
  have hC0 : 0 < C := by linarith
  have hR0 : 0 < R := by nlinarith [pow_pos hC0 3]
  have e : (1 - R / C) ^ 2 = (R - C) ^ 2 / C ^ 2 := by field_simp; ring
  rw [e]
  have hRC : C * 4 + 2 < C ^ 2 := by nlinarith
  have hRC2 : 4 * C ^ 2 + 2 * C < R := by nlinarith
  have hpos : 0 < (R - C) ^ 2 := by
    have : C < R := by nlinarith
    positivity
  have hden : 0 < s * ((R - C) ^ 2 / C ^ 2) * L := by positivity
  rw [div_lt_iff₀ hden]
  -- R < (1/2) s (R−C)²/C² L ⟸ 4 R C² < (R − C)² and s L ≥ 1/2
  have hsL : 1 / 2 ≤ s * L := by nlinarith
  have key : 4 * R * C ^ 2 < (R - C) ^ 2 := by nlinarith
  have : R = (4 * R * C ^ 2) / (4 * C ^ 2) := by field_simp; try ring
  calc R = (4 * R * C ^ 2) / (4 * C ^ 2) := this
    _ < (R - C) ^ 2 / (4 * C ^ 2) := by
        apply div_lt_div_of_pos_right key (by positivity)
    _ = 1 / 2 * (1 / 2 * ((R - C) ^ 2 / C ^ 2)) := by ring
    _ ≤ 1 / 2 * (s * L * ((R - C) ^ 2 / C ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply mul_le_mul_of_nonneg_right hsL (by positivity)
    _ = 1 / 2 * (s * ((R - C) ^ 2 / C ^ 2) * L) := by ring

/-- Case 2 (`σ − (w+1)x ≥ x`) gives `β < 1/2`. -/
theorem case2_bound {k n x : ℕ} {r c l s y : ℝ} (hk : 1 ≤ k) (hx : 8 * n ^ k < x) (hy : 4 ≤ y)
    (hyk : 2 * k < y) (hr : r ≤ (n : ℝ) ^ k * y ^ k) (hr0 : 0 ≤ r) (hc0 : 0 < c)
    (hl : (y - 1) ^ k ≤ l) (hs : (x : ℝ) ≤ s) (hρ0 : 0 ≤ r / c) (hρ : r / c < 1 / y ^ 2) :
    r / (s * (1 - r / c) ^ 2 * l) < 1 / 2 := by
  have hxR : (8 : ℝ) * n ^ k < x := by exact_mod_cast hx
  have hnk0 : (0 : ℝ) ≤ (n : ℝ) ^ k := by positivity
  have hx0 : (0 : ℝ) < x := by linarith
  have hy0 : 0 < y := by linarith
  have hy1 : 0 < y - 1 := by linarith
  have ht : 1 / y ^ 2 ≤ 1 / 16 := by
    apply one_div_le_one_div_of_le (by norm_num); nlinarith
  have hρ1 : r / c ≤ 1 / 16 := by linarith
  have h34 : (3 / 4 : ℝ) ≤ 1 - r / c := by linarith
  have hsq : (9 / 16 : ℝ) ≤ (1 - r / c) ^ 2 := by nlinarith
  have hl0 : 0 < l := lt_of_lt_of_le (pow_pos hy1 k) hl
  have hs0 : 0 < s := by linarith
  -- denominator ≥ x (9/16) (y−1)^k
  have hden : (x : ℝ) * (9 / 16) * (y - 1) ^ k ≤ s * (1 - r / c) ^ 2 * l := by
    apply mul_le_mul (mul_le_mul hs hsq (by norm_num) hs0.le) hl (pow_nonneg hy1.le k)
    exact mul_nonneg hs0.le (sq_nonneg _)
  have hden0 : 0 < (x : ℝ) * (9 / 16) * (y - 1) ^ k := by positivity
  have hstep : r / (s * (1 - r / c) ^ 2 * l) ≤ (n : ℝ) ^ k * y ^ k / ((x : ℝ) * (9 / 16) * (y - 1) ^ k) :=
    div_le_div₀ (mul_nonneg hnk0 (pow_nonneg hy0.le k)) hr hden0 hden
  -- (y/(y−1))^k ≤ 1 + 2k/y ≤ 2
  have h31 := lemma_3_1 hk (β := y) (by linarith)
  have h2 : ((y / (y - 1)) ^ k) ≤ 2 := by
    have : 2 * (k : ℝ) / y ≤ 1 := by rw [div_le_one hy0]; linarith
    linarith
  have hfac : (n : ℝ) ^ k * y ^ k / ((x : ℝ) * (9 / 16) * (y - 1) ^ k)
      = (16 / 9) * ((n : ℝ) ^ k / x) * (y / (y - 1)) ^ k := by
    rw [div_pow]; field_simp; try ring
  have hnkx : (n : ℝ) ^ k / x < 1 / 8 := by rw [div_lt_iff₀ hx0]; linarith
  have hnkx0 : 0 ≤ (n : ℝ) ^ k / x := by positivity
  calc r / (s * (1 - r / c) ^ 2 * l) ≤ _ := hstep
    _ = (16 / 9) * ((n : ℝ) ^ k / x) * (y / (y - 1)) ^ k := hfac
    _ ≤ (16 / 9) * (1 / 8) * 2 := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hnkx.le (by norm_num)) h2
          (pow_nonneg (div_nonneg hy0.le hy1.le) k) (by norm_num)
    _ < 1 / 2 := by norm_num

set_option maxHeartbeats 800000 in
/-- The packaged estimate (20)–(21): `|β − k!| < 1/2` for the Pell numbers of the proof and
`|s − C(n,k)| < 1/4`. -/
theorem beta_estimate {k n x w M : ℕ} {s : ℝ} (hk : 1 ≤ k) (hn : (2 * k) ^ (2 * k) < n)
    (hx : (2 * n) ^ (2 * n) < x) (hM : M = 16 * n * x * (w + 2) + 1)
    (hMx : 1 < M * x) (hMx1 : 1 < M * (x + 1)) (hMnx : 1 < M * n * x)
    (hs : |s - n.choose k| < 1 / 4) :
    |(ψ hMnx (k + 1) : ℝ) / (s * (1 - (ψ hMnx (k + 1) : ℝ) / ψ hMx1 (n + 1)) ^ 2 * ψ hMx (k + 1))
      - k.factorial| < 1 / 2 := by
  obtain ⟨hkn, hn5, hx8, hx2, hx10⟩ := basic_bounds hk hn hx
  have hk3 := add_three_le hk hn
  have hkk := mul_factorial_le hk hn
  have hM32 : 32 * n * x ≤ M := by
    rw [hM]
    have : 2 * (n * x) ≤ (w + 2) * (n * x) := Nat.mul_le_mul_right _ (by omega)
    nlinarith
  -- reals
  set y : ℝ := 2 * (M * x) with hy_def
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hMxR : (32 : ℝ) * n * x ≤ M * x := by
    have : (32 * n * x : ℝ) ≤ M := by exact_mod_cast hM32
    nlinarith
  have hMx2 : (2 : ℝ) ≤ M * x := by nlinarith
  have hy4 : 4 ≤ y := by rw [hy_def]; linarith
  have hy0 : 0 < y := by linarith
  have hkkR : (k : ℝ) * k.factorial ≤ n := by exact_mod_cast hkk
  have hkf1 : (1 : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_pos k
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hyk : 2 * (k : ℝ) < y := by rw [hy_def]; nlinarith
  have hy10 : 10 * (k : ℝ) * k.factorial ≤ y / 2 := by
    rw [hy_def]
    have : 10 * ((k : ℝ) * k.factorial) ≤ 10 * n := by linarith
    nlinarith
  have hz4 : 4 * (k : ℝ) * k.factorial ≤ n * y := by
    rw [hy_def]
    have : (n : ℝ) * (2 * (M * x)) ≥ n * 4 := by nlinarith
    nlinarith
  -- the Pell numbers, cast to ℝ
  have hr_up : ((ψ hMnx (k + 1) : ℕ) : ℝ) ≤ (2 * (M * n * x) : ℝ) ^ k := by
    have := ψ_succ_le_pow hMnx k; exact_mod_cast this
  have hr_lo : ((2 * (M * n * x) - 1 : ℕ) : ℝ) ^ k ≤ ((ψ hMnx (k + 1) : ℕ) : ℝ) := by
    have := pow_le_ψ_succ hMnx k; exact_mod_cast this
  have hc_lo : ((2 * (M * (x + 1)) - 1 : ℕ) : ℝ) ^ n ≤ ((ψ hMx1 (n + 1) : ℕ) : ℝ) := by
    have := pow_le_ψ_succ hMx1 n; exact_mod_cast this
  have hl_up : ((ψ hMx (k + 1) : ℕ) : ℝ) ≤ (2 * (M * x) : ℝ) ^ k := by
    have := ψ_succ_le_pow hMx k; exact_mod_cast this
  have hl_lo : ((2 * (M * x) - 1 : ℕ) : ℝ) ^ k ≤ ((ψ hMx (k + 1) : ℕ) : ℝ) := by
    have := pow_le_ψ_succ hMx k; exact_mod_cast this
  obtain ⟨r, hr_def⟩ : ∃ r : ℝ, r = ((ψ hMnx (k + 1) : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = ((ψ hMx1 (n + 1) : ℕ) : ℝ) := ⟨_, rfl⟩
  obtain ⟨l, hl_def⟩ : ∃ l : ℝ, l = ((ψ hMx (k + 1) : ℕ) : ℝ) := ⟨_, rfl⟩
  rw [← hr_def] at hr_up hr_lo
  rw [← hc_def] at hc_lo
  rw [← hl_def] at hl_up hl_lo
  rw [← hr_def, ← hc_def, ← hl_def]
  have e1 : ((2 * (M * n * x) - 1 : ℕ) : ℝ) = n * y - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; rw [hy_def]; ring
  have e2 : ((2 * (M * (x + 1)) - 1 : ℕ) : ℝ) = 2 * (M * (x + 1)) - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  have e3 : ((2 * (M * x) - 1 : ℕ) : ℝ) = y - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; rw [hy_def]
  rw [e1] at hr_lo; rw [e2] at hc_lo; rw [e3] at hl_lo
  have hr_up' : r ≤ (n : ℝ) ^ k * y ^ k := by
    calc r ≤ (2 * (M * n * x) : ℝ) ^ k := hr_up
      _ = (n : ℝ) ^ k * y ^ k := by rw [hy_def, ← mul_pow]; ring_nf
  have hl_up' : l ≤ y ^ k := by rw [hy_def]; exact hl_up
  have hny1 : 0 < (n : ℝ) * y - 1 := by nlinarith
  have hr0 : 0 < r := lt_of_lt_of_le (pow_pos hny1 k) hr_lo
  have hc_ge : y ^ n ≤ c := by
    refine le_trans (pow_le_pow_left₀ hy0.le ?_ n) hc_lo
    rw [hy_def]; nlinarith
  have hc0 : 0 < c := lt_of_lt_of_le (pow_pos hy0 n) hc_ge
  have hl0 : 0 < l := lt_of_lt_of_le (pow_pos (by linarith) k) hl_lo
  have hnk : (n : ℝ) ^ k < y := by
    have : (n : ℝ) ^ k < x := by exact_mod_cast (show n ^ k < x by omega)
    rw [hy_def]; nlinarith
  have hρ : r / c < 1 / y ^ 2 := rho_bound hk3 (by linarith) hnk hr_up' hc_ge hc0 hr0.le
  have hρ0 : 0 ≤ r / c := by positivity
  have hρ1 : r / c < 1 := by
    have : 1 / y ^ 2 ≤ 1 := by rw [div_le_one (by positivity)]; nlinarith
    linarith
  rw [abs_lt] at hs
  have hs_lo : (n.choose k : ℝ) - 1 / 4 ≤ s := by linarith
  have hs_hi : s ≤ (n.choose k : ℝ) + 1 / 4 := by linarith
  have hC5 : (5 : ℝ) * k.factorial ≤ n.choose k := by exact_mod_cast five_factorial_le_choose hk hn
  have hs0 : 0 < s := by linarith
  have hup := beta_upper hk hn hy4 hyk hy10 hr_up' hr0 hc0 hl_lo hs_lo hρ
  have hlo := beta_lower hk hn hy4 hz4 hr_lo hc0 hl0 hl_up' hs_hi hs0 hρ0 hρ1
  have h35 := lemma_3_5 hkf1
  have h36 := lemma_3_6 hkf1
  rw [abs_lt]
  constructor <;> linarith

end JSWW1976
