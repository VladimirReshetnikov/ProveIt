import Diophantine.Paper1978.Binomial
import Diophantine.Paper1976.MR

/-!
# Jones 1978, Lemma 2.8: the partial binomial `⌊(X+1)^N / X^Z⌋` from the Pell sequence

> **Lemma 2.8** (Matijasevič–Robinson [20]). For `0 < Y`, `4 N^Z < X` and `0 < Z < N`, the
> condition `Y = ⌊(X+1)^N / X^Z⌋` holds iff nonnegative integers `k, l, m, A, B, C, K, L, M`
> exist satisfying T0–T9.  Also T4–T9 imply that `A, B, C, K, L, M` are all `> 1`.

T0 `C = ψ_A(B)`; T1 `(M²−1)K² + 1 = □`; T2 `(M²X²−1)L² + 1 = □`; T3 `4(C − KLY)² < K²L²`;
T4 `M = 8N(X+Y) + 2`; T5 `K = N − Z + 1 + k(M−1)`; T6 `L = Z + 1 + l(MX−1)`;
T7 `A = M(X+1)`; T8 `B = N + 1`; T9 `C = m + B`.

> When `8N^Z < X` and `1 < Y` we may replace T3 by `5(C − KLY)² ≤ K²L²` and T4 by `M = 9NXY`.

The article cites the lemma from [20] without proof and states the variant without proof;
both are proved here by the ratio method, from a common core (`floor_core`,
`exists_core`).  With `K = ψ_M(N−Z+1)`, `L = ψ_{MX}(Z+1)`, `C = ψ_{M(X+1)}(N+1)` and the
bounds `(2a)^n (1 − n/(2a)) ≤ ψ_a(n+1) ≤ (2a)^n`, the quotient `C/(KL)` differs from
`ρ = (X+1)^N/X^Z` by at most `2ρε`, `ε = N/(2M)`, while the fractional part of `ρ` is
`< 1/4` (Lemma 2.6 with `4N^Z < X`); the size condition on `M` is only used through
`ε ≤ 1/32` and `2Yε ≤ 1/8`.  T3 then pins `Y` to `⌊ρ⌋`.  If the index of `K` or `L` were
not the least residue allowed by T5/T6, the Pell number would exceed `2C` and T3 would
force `Y = 0`.
-/

namespace Jones1978

open Pell Diophantine JSWW1976

/-- The conditions T0–T9. -/
structure TConds (N Z X Y k l m A B C K L M : ℕ) : Prop where
  T0 : ∀ hA : 1 < A, C = ψ hA B
  T1 : IsSquare ((M * M - 1) * K ^ 2 + 1)
  T2 : IsSquare ((M * X * (M * X) - 1) * L ^ 2 + 1)
  T3 : 4 * ((C : ℤ) - K * L * Y) ^ 2 < (K : ℤ) ^ 2 * L ^ 2
  T4 : M = 8 * N * (X + Y) + 2
  T5 : K = N - Z + 1 + k * (M - 1)
  T6 : L = Z + 1 + l * (M * X - 1)
  T7 : A = M * (X + 1)
  T8 : B = N + 1
  T9 : C = m + B

/-- The variant with T3' `5(C − KLY)² ≤ K²L²` and T4' `M = 9NXY` (used in the system
(1.3) of Theorem 3). -/
structure TConds' (N Z X Y k l m A B C K L M : ℕ) : Prop where
  T0 : ∀ hA : 1 < A, C = ψ hA B
  T1 : IsSquare ((M * M - 1) * K ^ 2 + 1)
  T2 : IsSquare ((M * X * (M * X) - 1) * L ^ 2 + 1)
  T3 : 5 * ((C : ℤ) - K * L * Y) ^ 2 ≤ (K : ℤ) ^ 2 * L ^ 2
  T4 : M = 9 * N * X * Y
  T5 : K = N - Z + 1 + k * (M - 1)
  T6 : L = Z + 1 + l * (M * X - 1)
  T7 : A = M * (X + 1)
  T8 : B = N + 1
  T9 : C = m + B

/-! ### Real bounds for `ψ` -/

theorem ψ_succ_le_pow_real {a : ℕ} (a1 : 1 < a) (n : ℕ) :
    (ψ a1 (n + 1) : ℝ) ≤ (2 * (a : ℝ)) ^ n := by
  have := ψ_succ_le_pow a1 n
  exact_mod_cast this

/-- `(2a)^n (1 − n/(2a)) ≤ ψ_a(n+1)` (Bernoulli applied to `(2a−1)^n ≤ ψ_a(n+1)`). -/
theorem pow_mul_le_ψ_succ_real {a : ℕ} (a1 : 1 < a) (n : ℕ) :
    (2 * (a : ℝ)) ^ n * (1 - (n : ℝ) / (2 * a)) ≤ ψ a1 (n + 1) := by
  have h := pow_le_ψ_succ a1 n
  have hR : ((2 * a - 1 : ℕ) : ℝ) ^ n ≤ ψ a1 (n + 1) := by exact_mod_cast h
  have ha : (0 : ℝ) < 2 * a := by
    have : (2 : ℝ) ≤ a := by exact_mod_cast a1
    linarith
  have hcast : ((2 * a - 1 : ℕ) : ℝ) = 2 * a - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcast] at hR
  have hx : (-2 : ℝ) ≤ -(1 / (2 * a)) := by
    have : (1 : ℝ) / (2 * a) ≤ 1 := by
      rw [div_le_one ha]
      have : (2 : ℝ) ≤ a := by exact_mod_cast a1
      linarith
    linarith
  have hB := one_add_mul_le_pow hx n
  have hfac : (2 * (a : ℝ) - 1) = (2 * a) * (1 + -(1 / (2 * a))) := by
    field_simp; ring
  calc (2 * (a : ℝ)) ^ n * (1 - (n : ℝ) / (2 * a))
      = (2 * (a : ℝ)) ^ n * (1 + n * (-(1 / (2 * a)))) := by ring
    _ ≤ (2 * (a : ℝ)) ^ n * (1 + -(1 / (2 * a))) ^ n :=
        mul_le_mul_of_nonneg_left hB (by positivity)
    _ = (2 * (a : ℝ) - 1) ^ n := by rw [hfac]; exact (mul_pow _ _ _).symm
    _ ≤ _ := hR

/-! ### The size argument for a wrong index -/

/-- If `4a ≤ b²` and `κ ≥ 2N + 1`, then `2 ψ_a(N+1) < ψ_b(κ)`. -/
theorem two_ψ_lt {a b N κ : ℕ} (a1 : 1 < a) (b1 : 1 < b) (hN : 1 ≤ N) (h4a : 4 * a ≤ b * b)
    (hκ : 2 * N + 1 ≤ κ) : 2 * ψ a1 (N + 1) < ψ b1 κ := by
  have h1 : ψ a1 (N + 1) ≤ (2 * a) ^ N := ψ_succ_le_pow a1 N
  have h2 : 2 * (2 * a) ^ N ≤ (4 * a) ^ N := by
    calc 2 * (2 * a) ^ N ≤ 2 ^ N * (2 * a) ^ N :=
          Nat.mul_le_mul_right _ (Nat.le_self_pow (by omega) 2)
      _ = (4 * a) ^ N := by rw [← mul_pow]; ring_nf
  have h3 : (4 * a) ^ N ≤ (b * b) ^ N := Nat.pow_le_pow_left h4a N
  have h4 : (b * b) ^ N < (2 * b - 1) ^ (2 * N) := by
    rw [show (b * b) ^ N = b ^ (2 * N) by rw [pow_mul, sq]]
    exact Nat.pow_lt_pow_left (by omega) (by omega)
  have h5 : (2 * b - 1) ^ (2 * N) ≤ (2 * b - 1) ^ (κ - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : (2 * b - 1) ^ (κ - 1) ≤ ψ b1 κ := by
    have := pow_le_ψ_succ b1 (κ - 1)
    rwa [Nat.sub_add_cancel (by omega)] at this
  omega

/-- `|C − KLY| < KL/2` is impossible when `2C < KL` and `Y ≥ 1`. -/
theorem T3_contra {C K L Y : ℕ} (hY : 1 ≤ Y) (h : 2 * C < K * L)
    (hT3 : |(C : ℝ) - K * L * Y| < K * L / 2) : False := by
  have hD : (2 * C : ℝ) < K * L := by exact_mod_cast h
  have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hKL : (0 : ℝ) < K * L := by
    have : (0 : ℝ) ≤ 2 * C := by positivity
    linarith
  have hDY : (K : ℝ) * L ≤ K * L * Y := le_mul_of_one_le_right hKL.le hY'
  have h1 := (abs_lt.1 hT3).1
  linarith

/-- T3 gives the real inequality. -/
theorem T3_real {C K L Y : ℕ} (hK : 1 ≤ K) (hL : 1 ≤ L)
    (T3 : 4 * ((C : ℤ) - K * L * Y) ^ 2 < (K : ℤ) ^ 2 * L ^ 2) :
    |(C : ℝ) - K * L * Y| < K * L / 2 := by
  have h1 : (4 * ((C : ℝ) - K * L * Y) ^ 2) < (K : ℝ) ^ 2 * L ^ 2 := by exact_mod_cast T3
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  apply abs_lt_of_sq_lt_sq _ (by positivity)
  nlinarith

/-- T3' gives the real inequality. -/
theorem T3'_real {C K L Y : ℕ} (hK : 1 ≤ K) (hL : 1 ≤ L)
    (T3 : 5 * ((C : ℤ) - K * L * Y) ^ 2 ≤ (K : ℤ) ^ 2 * L ^ 2) :
    |(C : ℝ) - K * L * Y| < K * L / 2 := by
  have h1 : (5 * ((C : ℝ) - K * L * Y) ^ 2) ≤ (K : ℝ) ^ 2 * L ^ 2 := by exact_mod_cast T3
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hL' : (1 : ℝ) ≤ L := by exact_mod_cast hL
  have hKL : (0 : ℝ) < K * L := by positivity
  apply abs_lt_of_sq_lt_sq _ (by positivity)
  nlinarith

/-! ### The real-number core -/

/-- With `Pρ(1−ε) ≤ C ≤ Pρ` and `P(1−ε) ≤ D ≤ P`, `|C − Dρ| ≤ 2Dρε`. -/
theorem core_estimate {C D P ρ ε : ℝ} (hP : 0 < P) (hρ : 0 ≤ ρ) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 2)
    (hC1 : P * ρ * (1 - ε) ≤ C) (hC2 : C ≤ P * ρ) (hD1 : P * (1 - ε) ≤ D) (hD2 : D ≤ P) :
    |C - D * ρ| ≤ 2 * D * ρ * ε := by
  have h2D : P ≤ 2 * D := by nlinarith
  have hρε : 0 ≤ ρ * ε := mul_nonneg hρ hε0
  have hPD := mul_le_mul_of_nonneg_right h2D hρε
  rw [abs_le]
  constructor
  · have : D * ρ ≤ P * ρ := mul_le_mul_of_nonneg_right hD2 hρ
    nlinarith
  · have : P * (1 - ε) * ρ ≤ D * ρ := mul_le_mul_of_nonneg_right hD1 hρ
    nlinarith

/-- T3 pins `Y` to `⌊ρ⌋`: from `|C − D(Q+f)| ≤ 2D(Q+f)ε`, `|C − DY| < D/2`, `0 ≤ f < 1/4`,
`ε ≤ 1/32` and `2Yε ≤ 1/8` follows `|Q − Y| < 1`. -/
theorem nearest_of_estimate {C D Y Q f ε : ℝ} (hD : 0 < D) (hY : 1 ≤ Y)
    (hf0 : 0 ≤ f) (hf : f < 1 / 4) (hQ : 0 ≤ Q) (hε0 : 0 ≤ ε) (hε32 : ε ≤ 1 / 32)
    (hYε : 2 * Y * ε ≤ 1 / 8)
    (h1 : |C - D * (Q + f)| ≤ 2 * D * (Q + f) * ε) (h2 : |C - D * Y| < D / 2) :
    -1 < Q - Y ∧ Q - Y < 1 := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = Q + f := ⟨_, rfl⟩
  rw [← hρ] at h1
  have hρ0 : 0 ≤ ρ := by rw [hρ]; linarith
  -- `|ρ − Y| < 2ρε + 1/2`
  have key : |ρ - Y| < 2 * ρ * ε + 1 / 2 := by
    have h3 : |D * (ρ - Y)| ≤ |C - D * ρ| + |C - D * Y| := by
      have : D * (ρ - Y) = (C - D * Y) - (C - D * ρ) := by ring
      rw [this]
      calc |(C - D * Y) - (C - D * ρ)| ≤ |C - D * Y| + |C - D * ρ| := abs_sub _ _
        _ = |C - D * ρ| + |C - D * Y| := add_comm _ _
    rw [abs_mul, abs_of_pos hD] at h3
    have h4 : D * |ρ - Y| < D * (2 * ρ * ε + 1 / 2) := by nlinarith
    exact lt_of_mul_lt_mul_left h4 hD.le
  -- `ρ − Y < 3/4`
  have hu : ρ - Y < 3 / 4 := by
    by_contra hcon
    push Not at hcon
    have h5 : ρ - Y < 2 * ρ * ε + 1 / 2 := (abs_lt.1 key).2
    have h6 : (ρ - Y) * (1 - 2 * ε) < 5 / 8 := by nlinarith
    have h7 : (3 / 4 : ℝ) * (1 - 2 * ε) ≤ (ρ - Y) * (1 - 2 * ε) :=
      mul_le_mul_of_nonneg_right hcon (by linarith)
    nlinarith
  have hρε : 2 * ρ * ε ≤ 11 / 64 := by
    have : (ρ - Y) * ε ≤ 3 / 4 * ε := mul_le_mul_of_nonneg_right hu.le hε0
    nlinarith
  have hkey := abs_lt.1 key
  constructor
  · have : -(2 * ρ * ε + 1 / 2) < ρ - Y := hkey.1
    linarith
  · have : ρ - Y < 2 * ρ * ε + 1 / 2 := hkey.2
    linarith

/-- Conversely `Y = ⌊ρ⌋` gives `|C − DY| ≤ (25/64) D`, which yields both T3 and T3'. -/
theorem estimate_of_floor {C D Y f ε : ℝ} (hD : 0 < D) (hY : 1 ≤ Y)
    (hf0 : 0 ≤ f) (hf : f < 1 / 4) (hε0 : 0 ≤ ε) (hε32 : ε ≤ 1 / 32) (hYε : 2 * Y * ε ≤ 1 / 8)
    (h1 : |C - D * (Y + f)| ≤ 2 * D * (Y + f) * ε) : |C - D * Y| ≤ 25 / 64 * D := by
  have hfε : f * ε ≤ 1 / 128 := by nlinarith
  have h3 : |C - D * Y| ≤ |C - D * (Y + f)| + D * f := by
    have : C - D * Y = (C - D * (Y + f)) + D * f := by ring
    rw [this]
    have hDf : 0 ≤ D * f := mul_nonneg hD.le hf0
    calc |C - D * (Y + f) + D * f| ≤ |C - D * (Y + f)| + |D * f| := abs_add_le _ _
      _ = |C - D * (Y + f)| + D * f := by rw [abs_of_nonneg hDf]
  have h4 : 2 * D * (Y + f) * ε + D * f ≤ 25 / 64 * D := by nlinarith
  linarith

/-! ### The estimates for `C = ψ_A(N+1)`, `K = ψ_M(N−Z+1)`, `L = ψ_{MX}(Z+1)` -/

/-- The quotient and remainder of `(X+1)^N` by `X^Z`, over `ℝ`. -/
theorem rho_split {N Z X : ℕ} (hZN : Z < N) (hX : 4 * N ^ Z < X) :
    ∃ f : ℝ, 0 ≤ f ∧ f < 1 / 4 ∧
      ((X : ℝ) + 1) ^ N / (X : ℝ) ^ Z = ((X + 1) ^ N / X ^ Z : ℕ) + f := by
  obtain ⟨v, hv, hv4⟩ := partial_binomial_rem (by norm_num : 0 < 4) hZN hX
  have hX0 : 0 < X := by
    have : 1 ≤ N ^ Z := Nat.one_le_pow _ _ (by omega)
    omega
  have hXZ : (0 : ℝ) < (X : ℝ) ^ Z := by positivity
  refine ⟨(v : ℝ) / (X : ℝ) ^ Z, by positivity, ?_, ?_⟩
  · rw [div_lt_iff₀ hXZ]
    have : (4 * v : ℝ) < (X : ℝ) ^ Z := by exact_mod_cast hv4
    linarith
  · have hvR : ((X : ℝ) + 1) ^ N = (((X + 1) ^ N / X ^ Z : ℕ) : ℝ) * (X : ℝ) ^ Z + v := by
      have := congrArg (fun m : ℕ => (m : ℝ)) hv
      push_cast at this ⊢
      exact this
    rw [hvR]
    field_simp

set_option maxHeartbeats 800000 in
/-- The main estimate `|C − KLρ| ≤ 2 KL ρ ε` with `ε = N/(2M)`, and `KL > 0`, for
`C = ψ_A(N+1)`, `K = ψ_M(N−Z+1)`, `L = ψ_{MX}(Z+1)`, assuming only `8N ≤ M`. -/
theorem pell_estimates {N Z X M A C K L : ℕ} (hZ : 0 < Z) (hZN : Z < N) (hX1 : 1 ≤ X)
    (hM8 : 8 * N ≤ M) (hA : A = M * (X + 1)) (hM1 : 1 < M)
    (hMX1 : 1 < M * X) (hA1 : 1 < A) (hC : C = ψ hA1 (N + 1)) (hK : K = ψ hM1 (N - Z + 1))
    (hL : L = ψ hMX1 (Z + 1)) :
    |(C : ℝ) - ((K : ℝ) * L) * (((X : ℝ) + 1) ^ N / (X : ℝ) ^ Z)|
        ≤ 2 * ((K : ℝ) * L) * (((X : ℝ) + 1) ^ N / (X : ℝ) ^ Z) * ((N : ℝ) / (2 * M)) ∧
      0 < (K : ℝ) * L := by
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ((X : ℝ) + 1) ^ N / (X : ℝ) ^ Z := ⟨_, rfl⟩
  obtain ⟨ε, hε⟩ : ∃ ε : ℝ, ε = (N : ℝ) / (2 * M) := ⟨_, rfl⟩
  rw [← hρ, ← hε]
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hM8R : (8 * N : ℝ) ≤ M := by exact_mod_cast hM8
  have hAR : (A : ℝ) = M * (X + 1) := by rw [hA]; push_cast; ring
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast (show 2 ≤ N by omega)
  have hZR : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hZNR : (Z : ℝ) < N := by exact_mod_cast hZN
  have hM0 : (0 : ℝ) < M := by linarith
  have hMN : (2 : ℝ) * N ≤ M := by linarith
  have hMA : (M : ℝ) ≤ A := by rw [hAR]; nlinarith
  have hA0 : (0 : ℝ) < A := by linarith
  have hMX : (M : ℝ) ≤ M * X := le_mul_of_one_le_right hM0.le hXR
  -- ε
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hε2 : ε ≤ 1 / 2 := by
    rw [hε, div_le_iff₀ (by positivity)]; linarith
  -- P
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = (2 * (M : ℝ)) ^ N * (X : ℝ) ^ Z := ⟨_, rfl⟩
  have hP0 : 0 < P := by rw [hP]; positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hPρ : P * ρ = (2 * (A : ℝ)) ^ N := by
    rw [hP, hρ, hAR]
    have hXZ : (X : ℝ) ^ Z ≠ 0 := by positivity
    rw [mul_div_assoc', mul_comm, ← mul_assoc, mul_div_assoc, div_self hXZ, mul_one, ← mul_pow]
    ring
  -- C
  have hC2 : (C : ℝ) ≤ P * ρ := by rw [hPρ, hC]; exact ψ_succ_le_pow_real hA1 N
  have hC1 : P * ρ * (1 - ε) ≤ C := by
    rw [hPρ, hC]
    have h := pow_mul_le_ψ_succ_real hA1 N
    have hle : (N : ℝ) / (2 * A) ≤ ε := by
      rw [hε]
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    calc (2 * (A : ℝ)) ^ N * (1 - ε) ≤ (2 * (A : ℝ)) ^ N * (1 - (N : ℝ) / (2 * A)) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ ≤ _ := h
  -- K and L
  have hKcast : ((N - Z : ℕ) : ℝ) = N - Z := by rw [Nat.cast_sub hZN.le]
  have hK2 : (K : ℝ) ≤ (2 * (M : ℝ)) ^ (N - Z) := by rw [hK]; exact ψ_succ_le_pow_real hM1 (N - Z)
  have hK1 : (2 * (M : ℝ)) ^ (N - Z) * (1 - ((N : ℝ) - Z) / (2 * M)) ≤ K := by
    rw [hK]
    have := pow_mul_le_ψ_succ_real hM1 (N - Z)
    rwa [hKcast] at this
  have hMXR : ((M * X : ℕ) : ℝ) = M * X := by push_cast; ring
  have hL2 : (L : ℝ) ≤ (2 * ((M : ℝ) * X)) ^ Z := by
    rw [hL]
    have := ψ_succ_le_pow_real hMX1 Z
    rwa [hMXR] at this
  have hL1 : (2 * ((M : ℝ) * X)) ^ Z * (1 - (Z : ℝ) / (2 * (M * X))) ≤ L := by
    rw [hL]
    have := pow_mul_le_ψ_succ_real hMX1 Z
    rwa [hMXR] at this
  have hprod : (2 * (M : ℝ)) ^ (N - Z) * (2 * ((M : ℝ) * X)) ^ Z = P := by
    rw [hP, show (2 * ((M : ℝ) * X)) = (2 * M) * X by ring, mul_pow (2 * (M : ℝ)) (X : ℝ) Z,
      ← mul_assoc, ← pow_add, Nat.sub_add_cancel hZN.le]
  have hα : ((N : ℝ) - Z) / (2 * M) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hβ : (Z : ℝ) / (2 * (M * X)) ≤ 1 := by
    rw [div_le_one (by positivity)]; linarith
  have hαβ : ((N : ℝ) - Z) / (2 * M) + (Z : ℝ) / (2 * (M * X)) ≤ ε := by
    rw [hε]
    have h1 : (Z : ℝ) / (2 * (M * X)) ≤ (Z : ℝ) / (2 * M) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)
    have h2 : ((N : ℝ) - Z) / (2 * M) + (Z : ℝ) / (2 * M) = (N : ℝ) / (2 * M) := by
      rw [← add_div]; congr 1; ring
    linarith
  have hD2 : (K : ℝ) * L ≤ P := by
    rw [← hprod]
    exact mul_le_mul hK2 hL2 (by positivity) (by positivity)
  have hD1 : P * (1 - ε) ≤ (K : ℝ) * L := by
    obtain ⟨α, hαdef⟩ : ∃ α : ℝ, α = ((N : ℝ) - Z) / (2 * M) := ⟨_, rfl⟩
    obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (Z : ℝ) / (2 * (M * X)) := ⟨_, rfl⟩
    rw [← hαdef] at hK1 hα hαβ
    rw [← hβdef] at hL1 hβ hαβ
    have hα0 : 0 ≤ α := by rw [hαdef]; positivity
    have hβ0 : 0 ≤ β := by rw [hβdef]; positivity
    have hαβ' : 1 - ε ≤ (1 - α) * (1 - β) := by
      have hexp : (1 - α) * (1 - β) = 1 - α - β + α * β := by ring
      have := mul_nonneg hα0 hβ0
      linarith
    calc P * (1 - ε) ≤ P * ((1 - α) * (1 - β)) := mul_le_mul_of_nonneg_left hαβ' hP0.le
      _ = ((2 * (M : ℝ)) ^ (N - Z) * (1 - α)) * ((2 * ((M : ℝ) * X)) ^ Z * (1 - β)) := by
          rw [← hprod]; ring
      _ ≤ _ := mul_le_mul hK1 hL1 (mul_nonneg (by positivity) (by linarith))
          (by positivity)
  have hD0 : 0 < (K : ℝ) * L := by
    have : 0 < P * (1 - ε) := mul_pos hP0 (by linarith)
    linarith
  exact ⟨core_estimate hP0 hρ0 hε0 hε2 hC1 hC2 hD1 hD2, hD0⟩

/-! ### The core of Lemma 2.8 -/

/-- Arithmetic facts about the sizes of `M`, `MX` and `A` (kept outside the main proof). -/
theorem index_bounds {N Z X M A : ℕ} (hX1 : 1 ≤ X) (hN2 : 2 ≤ N) (hZN : Z < N)
    (hM8 : 8 * N ≤ M) (hM4 : 4 * (X + 1) ≤ M) (hA : A = M * (X + 1)) :
    4 * A ≤ M * M ∧ 4 * A ≤ M * X * (M * X) ∧ N - Z + 1 < M - 1 ∧ Z + 1 < M * X - 1 := by
  have hM16 : 16 ≤ M := by omega
  have hMX : M ≤ M * X := Nat.le_mul_of_pos_right _ hX1
  refine ⟨?_, ?_, by omega, by omega⟩
  · rw [hA, show 4 * (M * (X + 1)) = M * (4 * (X + 1)) by ring]
    exact Nat.mul_le_mul_left _ hM4
  · rw [hA]
    have h1 : 4 * (M * (X + 1)) ≤ 8 * (M * X) := by nlinarith
    have h2 : 8 * (M * X) ≤ M * X * (M * X) := by
      have : 8 ≤ M * X := by omega
      nlinarith
    omega

/-- A Pell index that is not the least residue is at least `2N + 1`. -/
theorem index_large {κ c p b N : ℕ} (hp : κ = c + p * (b - 1)) (hp0 : 0 < p) (h8N : 8 * N ≤ b)
    (hb1 : 1 < b) : 2 * N + 1 ≤ κ := by
  have : b - 1 ≤ p * (b - 1) := Nat.le_mul_of_pos_left _ hp0
  omega

/-- The core of the sufficiency: T0–T2, T5–T7 with `8N ≤ M`, `4(X+1) ≤ M`, the real form of
T3, and `ε = N/(2M)` small, give `Y = ⌊(X+1)^N/X^Z⌋`. -/
theorem floor_core {N Z X Y k l A C K L M : ℕ} (hY : 0 < Y) (hX : 4 * N ^ Z < X)
    (hZ : 0 < Z) (hZN : Z < N) (hM8 : 8 * N ≤ M) (hM4 : 4 * (X + 1) ≤ M)
    (hA : A = M * (X + 1)) (hA1 : 1 < A) (hC : C = ψ hA1 (N + 1))
    (T1 : IsSquare ((M * M - 1) * K ^ 2 + 1)) (T2 : IsSquare ((M * X * (M * X) - 1) * L ^ 2 + 1))
    (T5 : K = N - Z + 1 + k * (M - 1)) (T6 : L = Z + 1 + l * (M * X - 1))
    (hε32 : (N : ℝ) / (2 * M) ≤ 1 / 32) (hYε : 2 * (Y : ℝ) * ((N : ℝ) / (2 * M)) ≤ 1 / 8)
    (hT3 : |(C : ℝ) - K * L * Y| < K * L / 2) :
    Y = (X + 1) ^ N / X ^ Z := by
  have hX1 : 1 ≤ X := by have := Nat.one_le_pow Z N (by omega); omega
  have hN2 : 2 ≤ N := by omega
  have hM1 : 1 < M := by omega
  have hMX1 : 1 < M * X := by nlinarith
  have hK1 : 1 ≤ K := by rw [T5]; omega
  have hL1 : 1 ≤ L := by rw [T6]; omega
  obtain ⟨h4aM, h4aMX, hNZM, hZMX⟩ := index_bounds hX1 hN2 hZN hM8 hM4 hA
  have hMX8N : 8 * N ≤ M * X := le_trans hM8 (Nat.le_mul_of_pos_right _ hX1)
  have hN1 : 1 ≤ N := by omega
  -- the index of `K` is `N − Z + 1`
  obtain ⟨κ, hκ⟩ := exists_eq_ψ_of_square hM1 T1
  have hKmod : ψ hM1 κ ≡ N - Z + 1 [MOD M - 1] := by
    rw [← hκ, T5]
    refine ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 ?_).symm
    rw [Nat.add_sub_cancel_left]
    exact dvd_mul_left _ _
  obtain ⟨p, hp⟩ := index_eq_of_modEq hM1 hNZM hKmod
  have hκeq : κ = N - Z + 1 := by
    rcases Nat.eq_zero_or_pos p with rfl | hp0
    · simpa using hp
    · exfalso
      have hκM : 2 * N + 1 ≤ κ := index_large hp hp0 hM8 hM1
      have hlt := two_ψ_lt hA1 hM1 hN1 h4aM hκM
      rw [← hC, ← hκ] at hlt
      have hKL : K ≤ K * L := Nat.le_mul_of_pos_right _ hL1
      exact T3_contra hY (lt_of_lt_of_le hlt hKL) hT3
  -- the index of `L` is `Z + 1`
  obtain ⟨lam, hlam⟩ := exists_eq_ψ_of_square hMX1 T2
  have hLmod : ψ hMX1 lam ≡ Z + 1 [MOD M * X - 1] := by
    rw [← hlam, T6]
    refine ((Nat.modEq_iff_dvd' (Nat.le_add_right _ _)).2 ?_).symm
    rw [Nat.add_sub_cancel_left]
    exact dvd_mul_left _ _
  obtain ⟨p', hp'⟩ := index_eq_of_modEq hMX1 hZMX hLmod
  have hlameq : lam = Z + 1 := by
    rcases Nat.eq_zero_or_pos p' with rfl | hp0
    · simpa using hp'
    · exfalso
      have hlamM : 2 * N + 1 ≤ lam := index_large hp' hp0 hMX8N hMX1
      have hlt := two_ψ_lt hA1 hMX1 hN1 h4aMX hlamM
      rw [← hC, ← hlam] at hlt
      have hKL : L ≤ K * L := Nat.le_mul_of_pos_left _ hK1
      exact T3_contra hY (lt_of_lt_of_le hlt hKL) hT3
  subst hκeq hlameq
  -- the real estimate
  obtain ⟨hest, hD0⟩ := pell_estimates hZ hZN hX1 hM8 hA hM1 hMX1 hA1 hC hκ hlam
  obtain ⟨f, hf0, hf, hρ⟩ := rho_split hZN hX
  rw [hρ] at hest
  have hT3R : |(C : ℝ) - ((K : ℝ) * L) * Y| < (K : ℝ) * L / 2 := by
    rw [show (C : ℝ) - ((K : ℝ) * L) * Y = (C : ℝ) - K * L * Y by ring]; exact hT3
  have := nearest_of_estimate hD0 (by exact_mod_cast hY) hf0 hf (by positivity) (by positivity)
    hε32 hYε hest hT3R
  have h1 : (((X + 1) ^ N / X ^ Z : ℕ) : ℝ) - Y < 1 := by linarith [this.2]
  have h2 : (-1 : ℝ) < (((X + 1) ^ N / X ^ Z : ℕ) : ℝ) - Y := by linarith [this.1]
  have h3 : ((((X + 1) ^ N / X ^ Z : ℕ) : ℤ) - Y : ℤ) < 1 := by exact_mod_cast h1
  have h4 : (-1 : ℤ) < ((((X + 1) ^ N / X ^ Z : ℕ) : ℤ) - Y : ℤ) := by exact_mod_cast h2
  omega

/-- The core of the necessity: for any `M` with `8N ≤ M`, `4(X+1) ≤ M` and `ε = N/(2M)`
small, the Pell numbers `C = ψ_A(N+1)`, `K = ψ_M(N−Z+1)`, `L = ψ_{MX}(Z+1)` satisfy
T0–T2, T5, T6, T9 and `|C − KLY| ≤ (25/64) KL`. -/
theorem exists_core {N Z X Y M : ℕ} (hY : 0 < Y) (hX : 4 * N ^ Z < X) (hZ : 0 < Z)
    (hZN : Z < N) (hM8 : 8 * N ≤ M) (hM4 : 4 * (X + 1) ≤ M)
    (hε32 : (N : ℝ) / (2 * M) ≤ 1 / 32) (hYε : 2 * (Y : ℝ) * ((N : ℝ) / (2 * M)) ≤ 1 / 8)
    (hYeq : Y = (X + 1) ^ N / X ^ Z) :
    ∃ k l m C K L, (∀ hA : 1 < M * (X + 1), C = ψ hA (N + 1)) ∧
      IsSquare ((M * M - 1) * K ^ 2 + 1) ∧ IsSquare ((M * X * (M * X) - 1) * L ^ 2 + 1) ∧
      K = N - Z + 1 + k * (M - 1) ∧ L = Z + 1 + l * (M * X - 1) ∧ C = m + (N + 1) ∧
      |(C : ℝ) - K * L * Y| ≤ 25 / 64 * (K * L) ∧ 1 ≤ K ∧ 1 ≤ L := by
  have hX1 : 1 ≤ X := by have := Nat.one_le_pow Z N (by omega); omega
  have hN2 : 2 ≤ N := by omega
  have hM1 : 1 < M := by omega
  have hMX1 : 1 < M * X := by nlinarith
  have hA1 : 1 < M * (X + 1) := by nlinarith
  -- K, L, C
  obtain ⟨K, hK⟩ : ∃ K, K = ψ hM1 (N - Z + 1) := ⟨_, rfl⟩
  obtain ⟨L, hL⟩ : ∃ L, L = ψ hMX1 (Z + 1) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C, C = ψ hA1 (N + 1) := ⟨_, rfl⟩
  have hKge : N - Z + 1 ≤ K := by rw [hK]; exact (lt_yn_of_two_le hM1 (by omega)).le
  have hLge : Z + 1 ≤ L := by rw [hL]; exact (lt_yn_of_two_le hMX1 (by omega)).le
  have hCge : N + 1 ≤ C := by rw [hC]; exact (lt_yn_of_two_le hA1 (by omega)).le
  obtain ⟨k, hk⟩ : M - 1 ∣ K - (N - Z + 1) := by
    have h := (ψ_modEq hM1 (N - Z + 1)).symm
    rw [← hK] at h
    exact (Nat.modEq_iff_dvd' hKge).1 h
  obtain ⟨l, hl⟩ : M * X - 1 ∣ L - (Z + 1) := by
    have h := (ψ_modEq hMX1 (Z + 1)).symm
    rw [← hL] at h
    exact (Nat.modEq_iff_dvd' hLge).1 h
  refine ⟨k, l, C - (N + 1), C, K, L, fun _ => hC, ?_, ?_,
    by rw [mul_comm]; omega, by rw [mul_comm]; omega, by omega, ?_, by omega, by omega⟩
  · rw [hK]; exact square_of_ψ hM1 _
  · rw [hL]; exact square_of_ψ hMX1 (Z + 1)
  · obtain ⟨hest, hD0⟩ := pell_estimates hZ hZN hX1 hM8 rfl hM1 hMX1 hA1 hC hK hL
    obtain ⟨f, hf0, hf, hρ⟩ := rho_split hZN hX
    rw [hρ, ← hYeq] at hest
    have h := estimate_of_floor hD0 (by exact_mod_cast hY) hf0 hf (by positivity) hε32 hYε hest
    rw [show (C : ℝ) - K * L * Y = (C : ℝ) - (K * L) * Y by ring]
    exact h

/-! ### Lemma 2.8 and its variant -/

/-- **Lemma 2.8**, sufficiency. -/
theorem floor_of_TConds {N Z X Y k l m A B C K L M : ℕ} (hY : 0 < Y) (hX : 4 * N ^ Z < X)
    (hZ : 0 < Z) (hZN : Z < N) (h : TConds N Z X Y k l m A B C K L M) :
    Y = (X + 1) ^ N / X ^ Z := by
  have hX1 : 1 ≤ X := by have := Nat.one_le_pow Z N (by omega); omega
  have hN2 : 2 ≤ N := by omega
  have hXY : 1 ≤ X + Y := by omega
  have h8 : 8 * N ≤ 8 * N * (X + Y) := Nat.le_mul_of_pos_right _ hXY
  have h4 : 4 * (X + 1) ≤ 8 * N * (X + Y) := by nlinarith
  have hM8 : 8 * N ≤ M := by rw [h.T4]; omega
  have hM4 : 4 * (X + 1) ≤ M := by rw [h.T4]; omega
  have hA1 : 1 < A := by rw [h.T7]; nlinarith
  have hK1 : 1 ≤ K := by rw [h.T5]; omega
  have hL1 : 1 ≤ L := by rw [h.T6]; omega
  have hMR : (M : ℝ) = 8 * N * (X + Y) + 2 := by rw [h.T4]; push_cast; ring
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hM0 : (0 : ℝ) < M := by rw [hMR]; positivity
  have hε32 : (N : ℝ) / (2 * M) ≤ 1 / 32 := by
    rw [div_le_iff₀ (by positivity), hMR]; nlinarith
  have hYε : 2 * (Y : ℝ) * ((N : ℝ) / (2 * M)) ≤ 1 / 8 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity), hMR]; nlinarith
  exact floor_core hY hX hZ hZN hM8 hM4 h.T7 hA1 (by rw [h.T0 hA1, h.T8]) h.T1 h.T2 h.T5 h.T6
    hε32 hYε (T3_real hK1 hL1 h.T3)

/-- **Lemma 2.8**, necessity. -/
theorem exists_TConds_of_floor {N Z X Y : ℕ} (hY : 0 < Y) (hX : 4 * N ^ Z < X) (hZ : 0 < Z)
    (hZN : Z < N) (hYeq : Y = (X + 1) ^ N / X ^ Z) :
    ∃ k l m A B C K L M, TConds N Z X Y k l m A B C K L M := by
  have hX1 : 1 ≤ X := by have := Nat.one_le_pow Z N (by omega); omega
  have hN2 : 2 ≤ N := by omega
  have hXY : 1 ≤ X + Y := by omega
  obtain ⟨M, hM⟩ : ∃ M, M = 8 * N * (X + Y) + 2 := ⟨_, rfl⟩
  have h8 : 8 * N ≤ 8 * N * (X + Y) := Nat.le_mul_of_pos_right _ hXY
  have h4 : 4 * (X + 1) ≤ 8 * N * (X + Y) := by nlinarith
  have hM8 : 8 * N ≤ M := by omega
  have hM4 : 4 * (X + 1) ≤ M := by omega
  have hMR : (M : ℝ) = 8 * N * (X + Y) + 2 := by rw [hM]; push_cast; ring
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hXR : (1 : ℝ) ≤ X := by exact_mod_cast hX1
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hM0 : (0 : ℝ) < M := by rw [hMR]; positivity
  have hε32 : (N : ℝ) / (2 * M) ≤ 1 / 32 := by
    rw [div_le_iff₀ (by positivity), hMR]; nlinarith
  have hYε : 2 * (Y : ℝ) * ((N : ℝ) / (2 * M)) ≤ 1 / 8 := by
    rw [mul_div_assoc', div_le_iff₀ (by positivity), hMR]; nlinarith
  obtain ⟨k, l, m, C, K, L, hC, T1, T2, T5, T6, T9, hest, hK1, hL1⟩ :=
    exists_core hY hX hZ hZN hM8 hM4 hε32 hYε hYeq
  refine ⟨k, l, m, M * (X + 1), N + 1, C, K, L, M, ⟨hC, T1, T2, ?_, hM, T5, T6, rfl, rfl, T9⟩⟩
  -- T3 from the estimate
  have hKL : (0 : ℝ) < (K : ℝ) * L := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    positivity
  have hsq : ((C : ℝ) - K * L * Y) ^ 2 ≤ (25 / 64 * ((K : ℝ) * L)) ^ 2 := by
    have h0 := abs_le.1 hest
    exact sq_le_sq' h0.1 h0.2
  have h4 : 4 * ((C : ℝ) - K * L * Y) ^ 2 < (K : ℝ) ^ 2 * L ^ 2 := by nlinarith
  exact_mod_cast h4

/-- **Lemma 2.8.** -/
theorem lemma_2_8 {N Z X Y : ℕ} (hY : 0 < Y) (hX : 4 * N ^ Z < X) (hZ : 0 < Z) (hZN : Z < N) :
    Y = (X + 1) ^ N / X ^ Z ↔ ∃ k l m A B C K L M, TConds N Z X Y k l m A B C K L M :=
  ⟨exists_TConds_of_floor hY hX hZ hZN,
    fun ⟨_, _, _, _, _, _, _, _, _, h⟩ => floor_of_TConds hY hX hZ hZN h⟩

/-- T4–T9 imply `A, B, C, K, L, M > 1`. -/
theorem TConds.gt_one {N Z X Y k l m A B C K L M : ℕ} (hZ : 0 < Z) (hZN : Z < N)
    (h : TConds N Z X Y k l m A B C K L M) :
    1 < A ∧ 1 < B ∧ 1 < C ∧ 1 < K ∧ 1 < L ∧ 1 < M := by
  have hM : 1 < M := by rw [h.T4]; omega
  refine ⟨by rw [h.T7]; nlinarith, by rw [h.T8]; omega, by rw [h.T9, h.T8]; omega, ?_, ?_, hM⟩
  · rw [h.T5]; omega
  · rw [h.T6]; omega

/-- The size facts for the variant `M = 9NXY`, `1 < Y`, `8N^Z < X`. -/
theorem variant_sizes {N Z X Y M : ℕ} (hY : 1 < Y) (hX : 8 * N ^ Z < X) (hZ : 0 < Z)
    (hZN : Z < N) (hM : M = 9 * N * X * Y) :
    8 * N ≤ M ∧ 4 * (X + 1) ≤ M ∧ (N : ℝ) / (2 * M) ≤ 1 / 32 ∧
      2 * (Y : ℝ) * ((N : ℝ) / (2 * M)) ≤ 1 / 8 := by
  have hX8 : 8 ≤ X := by have := Nat.one_le_pow Z N (by omega); omega
  have hN2 : 2 ≤ N := by omega
  have hXY : 16 ≤ X * Y := by nlinarith
  have hM8 : 8 * N ≤ M := by rw [hM]; nlinarith
  have hM4 : 4 * (X + 1) ≤ M := by rw [hM]; nlinarith
  have hMR : (M : ℝ) = 9 * N * X * Y := by rw [hM]; push_cast; ring
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hXR : (8 : ℝ) ≤ X := by exact_mod_cast hX8
  have hYR : (2 : ℝ) ≤ Y := by exact_mod_cast hY
  have hXYR : (16 : ℝ) ≤ X * Y := by exact_mod_cast hXY
  have hM0 : (0 : ℝ) < M := by rw [hMR]; positivity
  refine ⟨hM8, hM4, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity), hMR]
    have key : (N : ℝ) * 16 ≤ N * (X * Y) := mul_le_mul_of_nonneg_left hXYR (by positivity)
    nlinarith [key]
  · rw [mul_div_assoc', div_le_iff₀ (by positivity), hMR]
    have key : (N : ℝ) * Y * 8 ≤ N * Y * X := mul_le_mul_of_nonneg_left hXR (by positivity)
    nlinarith [key]

/-- **Lemma 2.8, variant**, sufficiency. -/
theorem floor_of_TConds' {N Z X Y k l m A B C K L M : ℕ} (hY : 1 < Y) (hX : 8 * N ^ Z < X)
    (hZ : 0 < Z) (hZN : Z < N) (h : TConds' N Z X Y k l m A B C K L M) :
    Y = (X + 1) ^ N / X ^ Z := by
  obtain ⟨hM8, hM4, hε32, hYε⟩ := variant_sizes hY hX hZ hZN h.T4
  have hX4 : 4 * N ^ Z < X := by omega
  have hX1 : 1 ≤ X := by omega
  have hA1 : 1 < A := by rw [h.T7]; nlinarith
  have hK1 : 1 ≤ K := by rw [h.T5]; omega
  have hL1 : 1 ≤ L := by rw [h.T6]; omega
  exact floor_core (by omega) hX4 hZ hZN hM8 hM4 h.T7 hA1 (by rw [h.T0 hA1, h.T8]) h.T1 h.T2
    h.T5 h.T6 hε32 hYε (T3'_real hK1 hL1 h.T3)

/-- **Lemma 2.8, variant**, necessity. -/
theorem exists_TConds'_of_floor {N Z X Y : ℕ} (hY : 1 < Y) (hX : 8 * N ^ Z < X) (hZ : 0 < Z)
    (hZN : Z < N) (hYeq : Y = (X + 1) ^ N / X ^ Z) :
    ∃ k l m A B C K L M, TConds' N Z X Y k l m A B C K L M := by
  obtain ⟨M, hM⟩ : ∃ M, M = 9 * N * X * Y := ⟨_, rfl⟩
  obtain ⟨hM8, hM4, hε32, hYε⟩ := variant_sizes hY hX hZ hZN hM
  have hX4 : 4 * N ^ Z < X := by omega
  obtain ⟨k, l, m, C, K, L, hC, T1, T2, T5, T6, T9, hest, hK1, hL1⟩ :=
    exists_core (by omega) hX4 hZ hZN hM8 hM4 hε32 hYε hYeq
  refine ⟨k, l, m, M * (X + 1), N + 1, C, K, L, M, ⟨hC, T1, T2, ?_, hM, T5, T6, rfl, rfl, T9⟩⟩
  have hKL : (0 : ℝ) < (K : ℝ) * L := by
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK1
    have : (1 : ℝ) ≤ L := by exact_mod_cast hL1
    positivity
  have hsq : ((C : ℝ) - K * L * Y) ^ 2 ≤ (25 / 64 * ((K : ℝ) * L)) ^ 2 := by
    have h0 := abs_le.1 hest
    exact sq_le_sq' h0.1 h0.2
  have h5 : 5 * ((C : ℝ) - K * L * Y) ^ 2 ≤ (K : ℝ) ^ 2 * L ^ 2 := by nlinarith
  exact_mod_cast h5

/-- **Lemma 2.8, the variant** used in (1.3): for `1 < Y`, `8N^Z < X`, `0 < Z < N`. -/
theorem lemma_2_8' {N Z X Y : ℕ} (hY : 1 < Y) (hX : 8 * N ^ Z < X) (hZ : 0 < Z) (hZN : Z < N) :
    Y = (X + 1) ^ N / X ^ Z ↔ ∃ k l m A B C K L M, TConds' N Z X Y k l m A B C K L M :=
  ⟨exists_TConds'_of_floor hY hX hZ hZN,
    fun ⟨_, _, _, _, _, _, _, _, _, h⟩ => floor_of_TConds' hY hX hZ hZN h⟩

end Jones1978
