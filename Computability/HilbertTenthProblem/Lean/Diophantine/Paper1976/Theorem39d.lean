import Diophantine.Paper1976.Theorem39c

/-!
# JSWW 1976, §3: Theorem 3.9, both directions

`theorem_3_9`: for `k ≥ 1`, `k + 1` is prime iff the system (I)–(XXI) has a
solution in nonnegative integers.
-/

namespace JSWW1976

open Pell Diophantine

set_option maxHeartbeats 1000000 in
/-- The real-number facts about the Pell numbers `C = ψ_{M(x+1)}(n+1)`, `L = ψ_{Mx}(k+1)`,
`R = ψ_{Mnx}(k+1)` used repeatedly, with `y = 2Mx`. -/
theorem pell_real_facts {k n x w M : ℕ} (hk : 1 ≤ k) (hn : (2 * k) ^ (2 * k) < n)
    (hx : (2 * n) ^ (2 * n) < x) (hM : M = 16 * n * x * (w + 2) + 1)
    (hMx : 1 < M * x) (hMx1 : 1 < M * (x + 1)) (hMnx : 1 < M * n * x) :
    4 ≤ (2 * (M * x) : ℝ) ∧ 2 * (k : ℝ) < 2 * (M * x) ∧
    ((ψ hMnx (k + 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ k * (2 * (M * x)) ^ k ∧
    (2 * (M * x) - 1 : ℝ) ^ k ≤ ((ψ hMx (k + 1) : ℕ) : ℝ) ∧
    ((ψ hMx (k + 1) : ℕ) : ℝ) ≤ (2 * (M * x) : ℝ) ^ k ∧
    (2 * (M * x) : ℝ) ^ n ≤ ((ψ hMx1 (n + 1) : ℕ) : ℝ) ∧
    ((ψ hMx1 (n + 1) : ℕ) : ℝ) ≤ (2 * (M * (x + 1)) : ℝ) ^ n ∧
    ((ψ hMnx (k + 1) : ℕ) : ℝ) / ((ψ hMx1 (n + 1) : ℕ) : ℝ) < 1 / (2 * (M * x) : ℝ) ^ 2 ∧
    (5 : ℝ) ≤ ((ψ hMx1 (n + 1) : ℕ) : ℝ) ∧ (1 : ℝ) ≤ ((ψ hMx (k + 1) : ℕ) : ℝ) ∧
    (0 : ℝ) < ((ψ hMnx (k + 1) : ℕ) : ℝ) := by
  obtain ⟨hkn, hn5, hx8, hx2, hx10⟩ := basic_bounds hk hn hx
  have hk3 := add_three_le hk hn
  have hM32 : 32 * n * x ≤ M := by
    rw [hM]
    have : 2 * (n * x) ≤ (w + 2) * (n * x) := Nat.mul_le_mul_right _ (by omega)
    linarith
  have hnx5 : 5 ≤ n * x := Nat.mul_le_mul hn5 (by omega) |>.trans' (by norm_num)
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hknR : (k : ℝ) < n := by exact_mod_cast hkn
  have hMxN : 32 * n * x ≤ M * x := by
    have := Nat.mul_le_mul_right x hM32
    have : 32 * n * x ≤ 32 * n * x * x := Nat.le_mul_of_pos_right _ (by omega)
    omega
  have hMxR : (32 : ℝ) * n * x ≤ M * x := by exact_mod_cast hMxN
  have hMx2 : (2 : ℝ) ≤ M * x := by
    have : 2 ≤ M * x := by omega
    exact_mod_cast this
  have hnxR : (5 : ℝ) ≤ n * x := by exact_mod_cast hnx5
  have hMx160 : (160 : ℝ) ≤ M * x := by linarith
  have hy4 : (4 : ℝ) ≤ 2 * (M * x) := by linarith
  have hyk : 2 * (k : ℝ) < 2 * (M * x) := by nlinarith
  have hr_up : ((ψ hMnx (k + 1) : ℕ) : ℝ) ≤ (2 * (M * n * x) : ℝ) ^ k := by
    have := ψ_succ_le_pow hMnx k; exact_mod_cast this
  have hr_lo : ((2 * (M * n * x) - 1 : ℕ) : ℝ) ^ k ≤ ((ψ hMnx (k + 1) : ℕ) : ℝ) := by
    have := pow_le_ψ_succ hMnx k; exact_mod_cast this
  have hc_lo : ((2 * (M * (x + 1)) - 1 : ℕ) : ℝ) ^ n ≤ ((ψ hMx1 (n + 1) : ℕ) : ℝ) := by
    have := pow_le_ψ_succ hMx1 n; exact_mod_cast this
  have hc_up : ((ψ hMx1 (n + 1) : ℕ) : ℝ) ≤ (2 * (M * (x + 1)) : ℝ) ^ n := by
    have := ψ_succ_le_pow hMx1 n; exact_mod_cast this
  have hl_up : ((ψ hMx (k + 1) : ℕ) : ℝ) ≤ (2 * (M * x) : ℝ) ^ k := by
    have := ψ_succ_le_pow hMx k; exact_mod_cast this
  have hl_lo : ((2 * (M * x) - 1 : ℕ) : ℝ) ^ k ≤ ((ψ hMx (k + 1) : ℕ) : ℝ) := by
    have := pow_le_ψ_succ hMx k; exact_mod_cast this
  have e1 : ((2 * (M * n * x) - 1 : ℕ) : ℝ) = 2 * (M * n * x) - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  have e2 : ((2 * (M * (x + 1)) - 1 : ℕ) : ℝ) = 2 * (M * (x + 1)) - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  have e3 : ((2 * (M * x) - 1 : ℕ) : ℝ) = 2 * (M * x) - 1 := by
    rw [Nat.cast_sub (by nlinarith)]; push_cast; ring
  rw [e1] at hr_lo; rw [e2] at hc_lo; rw [e3] at hl_lo
  have hr_up' : ((ψ hMnx (k + 1) : ℕ) : ℝ) ≤ (n : ℝ) ^ k * (2 * (M * x)) ^ k := by
    calc ((ψ hMnx (k + 1) : ℕ) : ℝ) ≤ (2 * (M * n * x) : ℝ) ^ k := hr_up
      _ = (n : ℝ) ^ k * (2 * (M * x)) ^ k := by rw [← mul_pow]; ring_nf
  have hMR1 : (1 : ℝ) ≤ M := by exact_mod_cast (show 1 ≤ M by omega)
  have hc_ge : (2 * (M * x) : ℝ) ^ n ≤ ((ψ hMx1 (n + 1) : ℕ) : ℝ) := by
    refine le_trans (pow_le_pow_left₀ (by positivity) ?_ n) hc_lo
    have : (2 * (M * (x + 1)) : ℝ) = 2 * (M * x) + 2 * M := by ring
    linarith
  have hc0 : (0 : ℝ) < ((ψ hMx1 (n + 1) : ℕ) : ℝ) := lt_of_lt_of_le (by positivity) hc_ge
  have hr0 : (0 : ℝ) < ((ψ hMnx (k + 1) : ℕ) : ℝ) := by
    have : (0 : ℝ) < 2 * (M * n * x) - 1 := by nlinarith
    exact lt_of_lt_of_le (pow_pos this k) hr_lo
  have hnk : (n : ℝ) ^ k < 2 * (M * x) := by
    have : (n : ℝ) ^ k < x := by exact_mod_cast (show n ^ k < x by omega)
    nlinarith
  have hρ := rho_bound hk3 (by linarith) hnk hr_up' hc_ge hc0 hr0.le
  have hc5 : (5 : ℝ) ≤ ((ψ hMx1 (n + 1) : ℕ) : ℝ) := by
    have : (5 : ℝ) ≤ (2 * (M * x) : ℝ) ^ n := by
      calc (5 : ℝ) ≤ 2 * (M * x) := by linarith
        _ = (2 * (M * x) : ℝ) ^ 1 := (pow_one _).symm
        _ ≤ (2 * (M * x) : ℝ) ^ n := pow_le_pow_right₀ (by linarith) (by omega)
    linarith
  have hl1 : (1 : ℝ) ≤ ((ψ hMx (k + 1) : ℕ) : ℝ) := by
    have : (1 : ℝ) ≤ (2 * (M * x) - 1 : ℝ) ^ k := one_le_pow₀ (by linarith)
    linarith
  exact ⟨hy4, hyk, hr_up', hl_lo, hl_up, hc_ge, hc_up, hρ, hc5, hl1, hr0⟩

/-- `β = R/(s(1−R/C)²L)` is nonpositive when `s < 0`. -/
theorem beta_nonpos_of_neg {R C L s : ℝ} (hR : 0 ≤ R) (hL : 0 < L) (hRC : R ≠ C) (hC : 0 < C)
    (hs : s < 0) : R / (s * (1 - R / C) ^ 2 * L) ≤ 0 := by
  have h1 : 0 < (1 - R / C) ^ 2 := by
    have : 1 - R / C ≠ 0 := by
      intro h
      apply hRC
      have : R / C = 1 := by linarith
      rw [div_eq_one_iff_eq hC.ne'] at this
      exact this
    positivity
  have hden : s * (1 - R / C) ^ 2 * L < 0 := by
    have : 0 < (1 - R / C) ^ 2 * L := mul_pos h1 hL
    nlinarith
  exact div_nonpos_of_nonneg_of_nonpos hR hden.le

set_option maxHeartbeats 4000000 in
/-- Theorem 3.9 needs only the growth supplied by its first two square tests. -/
theorem theorem_3_9_sufficiency_of_growth {k n x w m i j p l r z M A B C D E F G H I K L R S : ℕ}
    (hk : 1 ≤ k) (hS : GrowthSys39 k n x w m i j p l r z M A B C D E F G H I K L R S) :
    Nat.Prime (k + 1) := by
  obtain ⟨cI, cII, cIII, cIV, cV, cVI, cVII, cVIII, cIX, cX, cXI, cXII, cXIII, cXIVd, cXIV,
    cXV, cXVI, cXVII, cXVIII, cXIX, cXX, cXXI⟩ := hS
  have hn : (2 * k) ^ (2 * k) < n := cI
  have hx : (2 * n) ^ (2 * n) < x := cII
  obtain ⟨hkn, hn5, hx8, hx2, hx10⟩ := basic_bounds hk hn hx
  have hk3 := add_three_le hk hn
  -- sizes of M
  have hM32 : 32 * n * x ≤ M := by
    rw [cIII]
    have : 2 * (n * x) ≤ (w + 2) * (n * x) := Nat.mul_le_mul_right _ (by omega)
    linarith
  have hnx : 5 ≤ n * x := Nat.mul_le_mul hn5 (by omega) |>.trans' (by norm_num)
  have h32nx : 32 * n ≤ 32 * n * x := Nat.le_mul_of_pos_right _ (by omega)
  have hM1 : 1 < M := by omega
  have hMx : 1 < M * x := by have := Nat.le_mul_of_pos_right M (by omega : 0 < x); omega
  have hMx1 : 1 < M * (x + 1) := by have := Nat.le_mul_of_pos_right M (by omega : 0 < x + 1); omega
  have hMnx : 1 < M * n * x := by
    have := Nat.le_mul_of_pos_right M (by omega : 0 < n * x); rw [← mul_assoc] at this; omega
  have hM2n : 2 * n + 2 ≤ M := by omega
  have hMxge : M ≤ M * x := Nat.le_mul_of_pos_right M (by omega : 0 < x)
  have hMnxge : M ≤ M * n * x := by
    have := Nat.le_mul_of_pos_right M (by omega : 0 < n * x); rw [← mul_assoc] at this; exact this
  have h32x : 32 * x ≤ 32 * n * x := Nat.mul_le_mul_right x (by omega : 32 ≤ 32 * n)
  have hMx5 : M * x * 5 ≤ M * n * x := by
    rw [show M * n * x = M * x * n by ring]; exact Nat.mul_le_mul_left _ hn5
  have hMx1e : M * (x + 1) = M * x + M := by ring
  have hM32' : 32 * (n * x) ≤ M := by rw [← mul_assoc]; exact hM32
  have hxnx : x ≤ n * x := Nat.le_mul_of_pos_left x (by omega)
  -- (6): C = ψ_{M(x+1)}(n+1) by Lemma 3.8
  subst cIV cV
  have hB : 1 < n + 1 := by omega
  have hC0 : 0 < C := by omega
  have hCψ : ψ hMx1 (n + 1) = C := by
    rw [lemma_3_8 hMx1 hB hC0 0]
    exact ⟨i, j, D, E, F, G, H, I, ⟨cVII.1, cVII.2, by omega⟩, cVIII, by rw [cIX]; ring,
      cX, cXI, cXII, cXIII⟩
  -- (7)–(9): K, L, R are Pell numbers with indices ≡ n−k+1, k+1, k+1
  obtain ⟨tK, htK⟩ := exists_eq_ψ_of_square hM1 cXV
  obtain ⟨tL, htL⟩ := exists_eq_ψ_of_square hMx cXVI
  obtain ⟨tR, htR⟩ := exists_eq_ψ_of_square hMnx cXVII
  have hKmod : ψ hM1 tK ≡ n - k + 1 [MOD M - 1] := by
    rw [← htK]
    have e : K = (n - k + 1) + p * (M - 1) := by omega
    rw [e]
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
      ⟨p, by rw [Nat.add_sub_cancel_left]; ring⟩).symm
  obtain ⟨p', hp'⟩ := index_eq_of_modEq hM1 (by omega : n - k + 1 < M - 1) hKmod
  have hLmod : ψ hMx tL ≡ k + 1 [MOD M * x - 1] := by
    rw [← htL, cXIX]
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
      ⟨l, by rw [Nat.add_sub_cancel_left]; ring⟩).symm
  obtain ⟨l', hl'⟩ := index_eq_of_modEq hMx (by omega : k + 1 < M * x - 1) hLmod
  have hRmod : ψ hMnx tR ≡ k + 1 [MOD M * n * x - 1] := by
    rw [← htR, cXX]
    exact ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2
      ⟨r, by rw [Nat.add_sub_cancel_left]; ring⟩).symm
  obtain ⟨r', hr'⟩ := index_eq_of_modEq hMnx (by omega : k + 1 < M * n * x - 1) hRmod
  -- (XIV): β > S + 1/2 ≥ 1/2
  obtain ⟨hK0, hL0, hC0', hs0', hRC⟩ := cXIVd
  have hβ : |β C K L R w x - (S + 1)| < 1 / 2 :=
    abs_lt_of_sq_lt_sq (by rw [show (1 / 2 : ℝ) ^ 2 = 1 / 4 by norm_num]; exact cXIV) (by norm_num)
  have hβhalf : 1 / 2 < β C K L R w x := by
    rw [abs_lt] at hβ
    have hS0 : (0 : ℝ) ≤ S := by positivity
    linarith
  have hKR : (0 : ℝ) < K := by exact_mod_cast Nat.pos_of_ne_zero hK0
  have hLR : (0 : ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero hL0
  have hCR : (0 : ℝ) < C := by exact_mod_cast hC0
  have hRCR : (R : ℝ) ≠ C := by exact_mod_cast hRC
  -- s = σ − (w+1)x > 0, otherwise β ≤ 0
  have hs0 : 0 < σ C K L - (w + 1) * x := by
    rcases lt_trichotomy (σ C K L - (w + 1) * x) 0 with h | h | h
    · exfalso
      have := beta_nonpos_of_neg (R := R) (C := C) (L := L) (s := σ C K L - (w + 1) * x)
        (by positivity) hLR hRCR hCR h
      unfold β at hβhalf
      linarith
    · exact absurd h hs0'
    · exact h
  -- Case 1 or Case 2 (with s > 1/2 either way): first p' = l' = 0
  have hpl : p' = 0 ∧ l' = 0 := by
    by_contra hcon
    have hKL : ((2 * M - 1 : ℕ) : ℝ) ^ (n + M - 1) ≤ (K : ℝ) * L := by
      have h1 : (2 * M - 1) ^ (tK - 1) ≤ K := by rw [htK]; exact pow_le_ψ hM1 (by omega)
      have h2 : (2 * (M * x) - 1) ^ (tL - 1) ≤ L := by rw [htL]; exact pow_le_ψ hMx (by omega)
      have h3 : (2 * M - 1) ^ (tL - 1) ≤ (2 * (M * x) - 1) ^ (tL - 1) :=
        Nat.pow_le_pow_left (by omega) _
      have h4 : (2 * M - 1) ^ (n + M - 1) ≤ (2 * M - 1) ^ ((tK - 1) + (tL - 1)) := by
        apply Nat.pow_le_pow_right (by omega)
        have : M - 1 ≤ M * x - 1 := by omega
        rcases Nat.eq_zero_or_pos p' with hp0 | hp0
        · have hl0 : 0 < l' := by
            rcases Nat.eq_zero_or_pos l' with hl0 | hl0
            · exact absurd ⟨hp0, hl0⟩ hcon
            · exact hl0
          have : 1 * (M * x - 1) ≤ l' * (M * x - 1) := Nat.mul_le_mul_right _ hl0
          omega
        · have : 1 * (M - 1) ≤ p' * (M - 1) := Nat.mul_le_mul_right _ hp0
          omega
      have h5 : (2 * M - 1) ^ (n + M - 1) ≤ K * L := by
        calc (2 * M - 1) ^ (n + M - 1) ≤ (2 * M - 1) ^ ((tK - 1) + (tL - 1)) := h4
          _ = (2 * M - 1) ^ (tK - 1) * (2 * M - 1) ^ (tL - 1) := pow_add _ _ _
          _ ≤ K * L := Nat.mul_le_mul h1 (h3.trans h2)
      exact_mod_cast h5
    have hσ : σ C K L < 1 / 2 := by
      unfold σ
      refine sigma_small (x := x) hM2n (by omega) hKL (by positivity) ?_ hCR.le
      have := ψ_succ_le_pow hMx1 n
      rw [hCψ] at this
      exact_mod_cast this
    have : (1 : ℝ) ≤ (w + 1) * x := by
      have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
      have hw0 : (0 : ℝ) ≤ w := by positivity
      nlinarith
    linarith
  obtain ⟨rfl, rfl⟩ := hpl
  simp only [zero_mul, add_zero] at hp' hl'
  subst hp' hl'
  -- the estimate (11)
  have hsig := sigma_estimate hk hkn (by omega) (by omega) hM1 hMx hMx1
  rw [hCψ, ← htK, ← htL] at hsig
  obtain ⟨hσa, hσ2⟩ := hsig
  -- Pell facts
  obtain ⟨hy4, hyk, hr_up, hl_lo, hl_up, hc_ge, hc_up, hρ, hc5, hl1, hr0⟩ :=
    pell_real_facts hk hn hx cIII hMx hMx1 hMnx
  rw [hCψ] at hc_ge hc_up hρ hc5
  rw [← htL] at hl_lo hl_up hl1
  -- s > 1/2 in both cases
  have hs_half : 1 / 2 < σ C K L - (w + 1) * x := by
    rcases lt_or_ge (σ C K L - (w + 1) * x) x with hcase | hcase
    · have := case1_congruence hk hkn hn5 hx8 hx2 cIII hσa hσ2 hs0 hcase
      rw [abs_lt] at this
      have h5 : (5 : ℝ) ≤ n.choose k := by
        have := le_choose_of_lt hk hkn; exact_mod_cast (show 5 ≤ n.choose k by omega)
      linarith
    · have : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
      linarith
  -- r' = 0
  have hr0' : r' = 0 := by
    by_contra hcon
    have hr1 : 1 ≤ r' := Nat.pos_of_ne_zero hcon
    -- R ≥ (2Mnx − 1)^(Mnx) > C³
    have hRbig : (C : ℝ) ^ 3 < R := by
      have h1 : (2 * (M * n * x) - 1) ^ (tR - 1) ≤ R := by
        rw [htR]; exact pow_le_ψ hMnx (by omega)
      have h2 : (2 * (M * n * x) - 1) ^ (M * n * x) ≤ (2 * (M * n * x) - 1) ^ (tR - 1) := by
        apply Nat.pow_le_pow_right (by omega)
        have : 1 * (M * n * x - 1) ≤ r' * (M * n * x - 1) := Nat.mul_le_mul_right _ hr1
        omega
      have h3 : (2 * (M * (x + 1))) ^ (3 * n) < (2 * (M * n * x) - 1) ^ (M * n * x) := by
        have hb : 2 * (M * (x + 1)) ≤ 2 * (M * n * x) - 1 := by
          have : M * (x + 1) + 1 ≤ M * n * x := by omega
          omega
        have he : 3 * n < M * n * x := by
          have : 3 * n ≤ 32 * n * x := by omega
          omega
        calc (2 * (M * (x + 1))) ^ (3 * n) < (2 * (M * (x + 1))) ^ (M * n * x) :=
              Nat.pow_lt_pow_right (by nlinarith) he
          _ ≤ (2 * (M * n * x) - 1) ^ (M * n * x) := Nat.pow_le_pow_left hb _
      have h4 : C ^ 3 ≤ (2 * (M * (x + 1))) ^ (3 * n) := by
        have : C ≤ (2 * (M * (x + 1))) ^ n := by
          have := ψ_succ_le_pow hMx1 n; rw [hCψ] at this; exact this
        calc C ^ 3 ≤ ((2 * (M * (x + 1))) ^ n) ^ 3 := Nat.pow_le_pow_left this 3
          _ = (2 * (M * (x + 1))) ^ (3 * n) := by rw [← pow_mul]; ring_nf
      have : C ^ 3 < R := by omega
      exact_mod_cast this
    have := beta_lt_half_of_large_R hc5 hRbig hs_half hl1
    unfold β at hβhalf
    linarith
  subst hr0'
  simp only [zero_mul, add_zero] at hr'
  subst hr'
  rw [← htR] at hr_up hρ hr0
  -- Case 2 is excluded
  have hcase1 : σ C K L - (w + 1) * x < x := by
    by_contra hcon
    push_neg at hcon
    have := case2_bound hk hx8 hy4 hyk hr_up hr0.le hCR hl_lo hcon (by positivity) hρ
    unfold β at hβhalf
    linarith
  -- Case 1: |s − C(n,k)| < 1/4, hence |β − k!| < 1/2
  have hδ := case1_congruence hk hkn hn5 hx8 hx2 cIII hσa hσ2 hs0 hcase1
  have hbe := beta_estimate hk hn hx cIII hMx hMx1 hMnx hδ
  rw [hCψ, ← htL, ← htR] at hbe
  -- S + 1 = k!
  have hSk : S + 1 = k.factorial := by
    unfold β at hβ
    rw [abs_lt] at hβ hbe
    have h1 : ((S : ℝ) + 1) < k.factorial + 1 := by linarith
    have h2 : (k.factorial : ℝ) < (S : ℝ) + 1 + 1 := by linarith
    have h1' : S + 1 < k.factorial + 1 := by exact_mod_cast h1
    have h2' : k.factorial < S + 1 + 1 := by exact_mod_cast h2
    omega
  -- Wilson
  rw [lemma_2_9 hk]
  refine ⟨z + 1, ?_⟩
  rw [mul_comm]
  omega

/-- **Theorem 3.9, sufficiency.** -/
theorem theorem_3_9_sufficiency {k n x w m i j p l r z M A B C D E F G H I K L R S : ℕ}
    (hk : 1 ≤ k) (hS : Sys39 k n x w m i j p l r z M A B C D E F G H I K L R S) :
    Nat.Prime (k + 1) :=
  theorem_3_9_sufficiency_of_growth hk hS.toGrowthSys39

set_option maxHeartbeats 4000000 in
/-- Construct all remaining witnesses for any supplied sufficiently large
`n` and `x`. No second square condition on the supplied `x` is needed. -/
theorem theorem_3_9_necessity_of_growth {k n x : ℕ}
    (hk : 1 ≤ k) (hp : Nat.Prime (k + 1))
    (hn : (2 * k) ^ (2 * k) < n) (hx : (2 * n) ^ (2 * n) < x) :
    ∃ w m i j p l r z M A B C D E F G H I K L R S,
      GrowthSys39 k n x w m i j p l r z M A B C D E F G H I K L R S := by
  obtain ⟨hkn, hn5, hx8, hx2, hx10⟩ := basic_bounds hk hn hx
  have hk3 := add_three_le hk hn
  -- w from Lemma 3.3: ⌊(x+1)^n/x^k⌋ = C(n,k) + (w+1) x
  obtain ⟨w', hw'1, hfloor, hfrac⟩ := lemma_3_3 hkn hx2
  obtain ⟨w, rfl⟩ : ∃ w, w' = w + 1 := ⟨w' - 1, by omega⟩
  -- M, A, B, C, m
  obtain ⟨M, hM⟩ : ∃ M, M = 16 * n * x * (w + 2) + 1 := ⟨_, rfl⟩
  have hM32 : 32 * n * x ≤ M := by
    rw [hM]
    have : 2 * (n * x) ≤ (w + 2) * (n * x) := Nat.mul_le_mul_right _ (by omega)
    linarith
  have hnx : 5 ≤ n * x := Nat.mul_le_mul hn5 (by omega) |>.trans' (by norm_num)
  have h32nx : 32 * n ≤ 32 * n * x := Nat.le_mul_of_pos_right _ (by omega)
  have hM1 : 1 < M := by omega
  have hMx : 1 < M * x := by have := Nat.le_mul_of_pos_right M (by omega : 0 < x); omega
  have hMx1 : 1 < M * (x + 1) := by have := Nat.le_mul_of_pos_right M (by omega : 0 < x + 1); omega
  have hMnx : 1 < M * n * x := by
    have := Nat.le_mul_of_pos_right M (by omega : 0 < n * x); rw [← mul_assoc] at this; omega
  obtain ⟨C, hC⟩ : ∃ C, C = ψ hMx1 (n + 1) := ⟨_, rfl⟩
  have hBC : n + 1 ≤ C := by rw [hC]; exact yn_ge_n hMx1 (n + 1)
  have hC0 : 0 < C := by omega
  obtain ⟨i, j, D, E, F, G, H, I, hMR⟩ := (lemma_3_8 hMx1 (by omega) hC0 0).1 hC.symm
  obtain ⟨⟨hDFI, hFHC, -⟩, hA2, hA3, hA4, hA5, hA6, hA7⟩ := hMR
  -- K, L, R and the indices p, l, r
  obtain ⟨K, hK⟩ : ∃ K, K = ψ hM1 (n - k + 1) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ψ hMx (k + 1) := ⟨_, rfl⟩
  obtain ⟨R, hR⟩ : ∃ R, R = ψ hMnx (k + 1) := ⟨_, rfl⟩
  have hKge : n - k + 1 ≤ K := by rw [hK]; exact yn_ge_n hM1 _
  have hLge : k + 1 ≤ L := by rw [hL]; exact yn_ge_n hMx _
  have hRge : k + 1 ≤ R := by rw [hR]; exact yn_ge_n hMnx _
  have hKmod : K ≡ n - k + 1 [MOD M - 1] := by rw [hK]; exact ψ_modEq hM1 _
  have hLmod : L ≡ k + 1 [MOD M * x - 1] := by rw [hL]; exact ψ_modEq hMx _
  have hRmod : R ≡ k + 1 [MOD M * n * x - 1] := by rw [hR]; exact ψ_modEq hMnx _
  obtain ⟨p, hpK⟩ := (Nat.modEq_iff_dvd' hKge).1 hKmod.symm
  obtain ⟨l, hlL⟩ := (Nat.modEq_iff_dvd' hLge).1 hLmod.symm
  obtain ⟨r, hrR⟩ := (Nat.modEq_iff_dvd' hRge).1 hRmod.symm
  -- S and z from Wilson's theorem
  have hW := (lemma_2_9 hk).1 hp
  obtain ⟨z1, hz1⟩ := hW
  have hz1pos : 1 ≤ z1 := by
    rcases Nat.eq_zero_or_pos z1 with h | h
    · rw [h] at hz1; have := Nat.factorial_pos k; omega
    · exact h
  obtain ⟨z, rfl⟩ : ∃ z, z1 = z + 1 := ⟨z1 - 1, by omega⟩
  obtain ⟨S, hS⟩ : ∃ S, S = k.factorial - 1 := ⟨_, rfl⟩
  have hS1 : S + 1 = k.factorial := by rw [hS, Nat.sub_add_cancel (Nat.factorial_pos k)]
  -- the real estimates: (11), (23), and |β − k!| < 1/2
  have hsig := sigma_estimate hk hkn (by omega) (by omega) hM1 hMx hMx1
  rw [← hC, ← hK, ← hL] at hsig
  obtain ⟨hσa, hσ2⟩ := hsig
  obtain ⟨hy4, hyk, hr_up, hl_lo, hl_up, hc_ge, hc_up, hρ, hc5, hl1, hr0⟩ :=
    pell_real_facts hk hn hx hM hMx hMx1 hMnx
  rw [← hC] at hc_ge hc_up hρ hc5
  rw [← hL] at hl_lo hl_up hl1
  rw [← hR] at hr_up hρ hr0
  -- (23): (n/M) a < 1/16 and hence C(n,k) − 1/16 < s < C(n,k) + 3/16
  set a : ℝ := ((x : ℝ) + 1) ^ n / (x : ℝ) ^ k with ha_def
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast (show 1 ≤ x by omega)
  have hnR : (5 : ℝ) ≤ n := by exact_mod_cast hn5
  have ha0 : 0 < a := by positivity
  have hT : (((n.choose k + (w + 1) * x : ℕ) : ℤ) : ℝ) = (n.choose k : ℝ) + (w + 1) * x := by
    push_cast; ring
  have hfl : (n.choose k : ℝ) + (w + 1) * x ≤ a := by
    have := Int.floor_le a; rw [hfloor, hT] at this; exact this
  have hfr : a - ((n.choose k : ℝ) + (w + 1) * x) < 1 / 8 := by
    have := hfrac; push_cast at this; exact this
  have hCx : (n.choose k : ℝ) * 8 < x := by
    have h1 := choose_le_pow' n k
    exact_mod_cast (show n.choose k * 8 < x by nlinarith)
  have hC5 : (5 : ℝ) ≤ n.choose k := by
    have := le_choose_of_lt hk hkn; exact_mod_cast (show 5 ≤ n.choose k by omega)
  have hMR : (M : ℝ) = 16 * n * x * (w + 2) + 1 := by rw [hM]; push_cast; ring
  have hM0 : (0 : ℝ) < M := by rw [hMR]; positivity
  have hε : (n : ℝ) / M * a < 1 / 16 := by
    -- a < (w+2) x, so 16 n a < 16 n x (w+2) < M
    have h1 : a < (w + 2) * x := by linarith
    have h2 : 16 * (n : ℝ) * a < 16 * n * ((w + 2) * x) :=
      mul_lt_mul_of_pos_left h1 (by positivity)
    have h3 : 16 * (n : ℝ) * a < M := by rw [hMR]; linarith
    rw [div_mul_eq_mul_div, div_lt_iff₀ hM0]
    linarith
  have hsub : |σ C K L - a| < 1 / 16 := lt_of_le_of_lt hσa hε
  rw [abs_lt] at hsub
  have hs_lo : (n.choose k : ℝ) - 1 / 16 < σ C K L - (w + 1) * x := by linarith
  have hs_hi : σ C K L - (w + 1) * x < (n.choose k : ℝ) + 3 / 16 := by linarith
  have hs0 : 0 < σ C K L - (w + 1) * x := by linarith
  have hδ : |σ C K L - (w + 1) * x - n.choose k| < 1 / 4 := by
    rw [abs_lt]; constructor <;> linarith
  have hbe := beta_estimate hk hn hx hM hMx hMx1 hMnx hδ
  rw [← hC, ← hL, ← hR] at hbe
  have hRC : R ≠ C := by
    intro h
    rw [h, div_self (by positivity)] at hρ
    have : (1 : ℝ) / (2 * (M * x)) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  -- assemble
  refine ⟨w, C - (n + 1), i, j, p, l, r, z, M, M * (x + 1), n + 1, C, D, E, F, G, H, I,
    K, L, R, S, ?_⟩
  refine ⟨hn, hx, hM, rfl, rfl, by omega, ⟨hDFI, hFHC⟩, hA2, by rw [hA3]; ring, hA4, hA5, hA6,
    hA7, ⟨?_, ?_, by omega, hs0.ne', hRC⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hK]; exact (ψ_pos_of_pos hM1 (by omega)).ne'
  · rw [hL]; exact (ψ_pos_of_pos hMx (by omega)).ne'
  · -- (XIV)
    unfold β
    rw [abs_lt] at hbe
    have e : ((S : ℝ) + 1) = k.factorial := by exact_mod_cast hS1
    rw [e]
    have h1 : -(1 / 2 : ℝ) < _ - k.factorial := hbe.1
    have h2 : _ - (k.factorial : ℝ) < 1 / 2 := hbe.2
    have := sq_lt_sq' h1 h2
    norm_num at this ⊢
    linarith
  · rw [hK]; exact square_of_ψ hM1 _
  · rw [hL]; exact square_of_ψ hMx _
  · rw [hR]; exact square_of_ψ hMnx _
  · rw [mul_comm p]; omega
  · rw [mul_comm l]; omega
  · rw [mul_comm r]; omega
  · rw [hS, mul_comm (z + 1)]; have := Nat.factorial_pos k; omega

/-- **Theorem 3.9, necessity.** -/
theorem theorem_3_9_necessity {k : ℕ} (hk : 1 ≤ k) (hp : Nat.Prime (k + 1)) :
    ∃ n x w m i j p l r z M A B C D E F G H I K L R S,
      Sys39 k n x w m i j p l r z M A B C D E F G H I K L R S := by
  obtain ⟨n, -, cI⟩ := exists_U_square (2 * k) 0
  obtain ⟨x, -, cII⟩ := exists_U_square (2 * n) 0
  obtain ⟨w, m, i, j, p, l, r, z, M, A, B, C, D, E, F, G, H, I, K, L, R, S, h⟩ :=
    theorem_3_9_necessity_of_growth hk hp (lt_of_U_square cI) (lt_of_U_square cII)
  exact ⟨n, x, w, m, i, j, p, l, r, z, M, A, B, C, D, E, F, G, H, I, K, L, R, S,
    h.toSys39 cI cII⟩

/-- **Theorem 3.9.** For `k ≥ 1`, `k+1` is prime iff the system (I)–(XXI) is solvable. -/
theorem theorem_3_9 {k : ℕ} (hk : 1 ≤ k) :
    Nat.Prime (k + 1) ↔ ∃ n x w m i j p l r z M A B C D E F G H I K L R S,
      Sys39 k n x w m i j p l r z M A B C D E F G H I K L R S :=
  ⟨theorem_3_9_necessity hk, fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
    _, _, _, _, hS⟩ => theorem_3_9_sufficiency hk hS⟩

end JSWW1976
