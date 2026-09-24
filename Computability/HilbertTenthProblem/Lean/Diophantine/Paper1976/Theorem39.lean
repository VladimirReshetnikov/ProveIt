import Diophantine.Paper1976.MR
import Diophantine.Paper1976.Wilson
import Mathlib.Tactic

/-!
# JSWW 1976, §3: Theorem 3.9 (primes via the ratio method)

> **Theorem 3.9.** For any positive integer `k`, `k+1` is prime iff the system
> (I)–(XXI) has a solution in nonnegative integers (the rational expression in
> (XIV) must be defined).

The unknowns are `n, x, w, m, i, j, p, l, r, z` together with the abbreviations
`M, A, B, C, D, E, F, G, H, I, K, L, R, S` (which the article eliminates by
substitution afterwards).  The square conditions `… = □` are `IsSquare`; the
equations involving `A² − 1`, `M² − 1`, `F − A`, `n − k` are written without
natural-number subtraction, which is their integer meaning.  Condition (XIV) is
stated over `ℝ` with the explicit requirement that the denominators are nonzero.

This file: the system, and the estimates (2)–(5) and (11) of the proof.
-/

namespace JSWW1976

open Pell Diophantine

/-- `σ = C/(KL)`. -/
noncomputable def σ (C K L : ℕ) : ℝ := (C : ℝ) / ((K : ℝ) * L)

/-- `β = R / ((σ − (w+1)x)(1 − R/C)² L)`. -/
noncomputable def β (C K L R w x : ℕ) : ℝ :=
  (R : ℝ) / ((σ C K L - (w + 1) * x) * (1 - (R : ℝ) / C) ^ 2 * L)

/-- The system (I)–(XXI) of Theorem 3.9. -/
structure Sys39 (k n x w m i j p l r z M A B C D E F G H I K L R S : ℕ) : Prop where
  cI : IsSquare (U (2 * k) n)
  cII : IsSquare (U (2 * n) x)
  cIII : M = 16 * n * x * (w + 2) + 1
  cIV : A = M * (x + 1)
  cV : B = n + 1
  cVI : C = m + B
  cVII : IsSquare (D * F * I) ∧ (F : ℤ) ∣ (H : ℤ) - C
  cVIII : D + C ^ 2 = A ^ 2 * C ^ 2 + 1
  cIX : E = 2 * (i + 1) * D * C ^ 2
  cX : F + E ^ 2 = A ^ 2 * E ^ 2 + 1
  cXI : G + F * A = A + F ^ 2
  cXII : H = B + 2 * (j + 1) * C
  cXIII : I + H ^ 2 = G ^ 2 * H ^ 2 + 1
  cXIV_def : K ≠ 0 ∧ L ≠ 0 ∧ C ≠ 0 ∧ σ C K L - (w + 1) * x ≠ 0 ∧ R ≠ C
  cXIV : (β C K L R w x - (S + 1)) ^ 2 < 1 / 4
  cXV : IsSquare ((M * M - 1) * K ^ 2 + 1)
  cXVI : IsSquare ((M * x * (M * x) - 1) * L ^ 2 + 1)
  cXVII : IsSquare ((M * n * x * (M * n * x) - 1) * R ^ 2 + 1)
  cXVIII : K + k = n + 1 + p * (M - 1)
  cXIX : L = k + 1 + l * (M * x - 1)
  cXX : R = k + 1 + r * (M * n * x - 1)
  cXXI : S + 2 = (z + 1) * (k + 1)

/-- The same ratio system, with the first two square tests replaced by
the growth bounds they supply. This is the interface needed for (24). -/
structure GrowthSys39 (k n x w m i j p l r z M A B C D E F G H I K L R S : ℕ) : Prop where
  cI : (2 * k) ^ (2 * k) < n
  cII : (2 * n) ^ (2 * n) < x
  cIII : M = 16 * n * x * (w + 2) + 1
  cIV : A = M * (x + 1)
  cV : B = n + 1
  cVI : C = m + B
  cVII : IsSquare (D * F * I) ∧ (F : ℤ) ∣ (H : ℤ) - C
  cVIII : D + C ^ 2 = A ^ 2 * C ^ 2 + 1
  cIX : E = 2 * (i + 1) * D * C ^ 2
  cX : F + E ^ 2 = A ^ 2 * E ^ 2 + 1
  cXI : G + F * A = A + F ^ 2
  cXII : H = B + 2 * (j + 1) * C
  cXIII : I + H ^ 2 = G ^ 2 * H ^ 2 + 1
  cXIV_def : K ≠ 0 ∧ L ≠ 0 ∧ C ≠ 0 ∧ σ C K L - (w + 1) * x ≠ 0 ∧ R ≠ C
  cXIV : (β C K L R w x - (S + 1)) ^ 2 < 1 / 4
  cXV : IsSquare ((M * M - 1) * K ^ 2 + 1)
  cXVI : IsSquare ((M * x * (M * x) - 1) * L ^ 2 + 1)
  cXVII : IsSquare ((M * n * x * (M * n * x) - 1) * R ^ 2 + 1)
  cXVIII : K + k = n + 1 + p * (M - 1)
  cXIX : L = k + 1 + l * (M * x - 1)
  cXX : R = k + 1 + r * (M * n * x - 1)
  cXXI : S + 2 = (z + 1) * (k + 1)

theorem Sys39.toGrowthSys39 {k n x w m i j p l r z M A B C D E F G H I K L R S : ℕ}
    (h : Sys39 k n x w m i j p l r z M A B C D E F G H I K L R S) :
    GrowthSys39 k n x w m i j p l r z M A B C D E F G H I K L R S :=
  ⟨lt_of_U_square h.cI, lt_of_U_square h.cII, h.cIII, h.cIV, h.cV, h.cVI,
    h.cVII, h.cVIII, h.cIX, h.cX, h.cXI, h.cXII, h.cXIII, h.cXIV_def, h.cXIV,
    h.cXV, h.cXVI, h.cXVII, h.cXVIII, h.cXIX, h.cXX, h.cXXI⟩

theorem GrowthSys39.toSys39 {k n x w m i j p l r z M A B C D E F G H I K L R S : ℕ}
    (h : GrowthSys39 k n x w m i j p l r z M A B C D E F G H I K L R S)
    (hI : IsSquare (U (2 * k) n)) (hII : IsSquare (U (2 * n) x)) :
    Sys39 k n x w m i j p l r z M A B C D E F G H I K L R S :=
  ⟨hI, hII, h.cIII, h.cIV, h.cV, h.cVI, h.cVII, h.cVIII, h.cIX, h.cX,
    h.cXI, h.cXII, h.cXIII, h.cXIV_def, h.cXIV, h.cXV, h.cXVI, h.cXVII,
    h.cXVIII, h.cXIX, h.cXX, h.cXXI⟩

/-! ### The basic size bounds (2)–(5) -/

/-- The bounds on `n` and `x` implied by (I) and (II): `k < n`, `5 ≤ n`, `x > 8 n^k`,
`x > 8·2^n`, `x ≥ 10^10`. -/
theorem basic_bounds {k n x : ℕ} (hk : 1 ≤ k) (hn : (2 * k) ^ (2 * k) < n)
    (hx : (2 * n) ^ (2 * n) < x) :
    k < n ∧ 5 ≤ n ∧ 8 * n ^ k < x ∧ 8 * 2 ^ n < x ∧ 10 ^ 10 ≤ x := by
  have h4 : 4 ≤ (2 * k) ^ (2 * k) := by
    calc 4 = (2 * 1) ^ (2 * 1) := by norm_num
      _ ≤ (2 * k) ^ (2 * 1) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (2 * k) ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
  have hkn : k < n := by
    have : k ≤ (2 * k) ^ (2 * k) := by
      calc k ≤ 2 * k := by omega
        _ = (2 * k) ^ 1 := (pow_one _).symm
        _ ≤ (2 * k) ^ (2 * k) := Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hn5 : 5 ≤ n := by omega
  have hn0 : 0 < n := by omega
  have hnn : 0 < n ^ n * n ^ n := Nat.mul_pos (Nat.pow_pos hn0) (Nat.pow_pos hn0)
  -- (2n)^(2n) = 4^n n^n n^n
  have h1 : 8 * n ^ k < (2 * n) ^ (2 * n) := by
    have e : (2 * n) ^ (2 * n) = (2 ^ n * 2 ^ n) * (n ^ n * n ^ n) := by ring
    rw [e]
    have hnk : n ^ k ≤ n ^ n := Nat.pow_le_pow_right hn0 hkn.le
    have h4n : 16 ≤ 2 ^ n * 2 ^ n := by
      have : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      nlinarith
    have hnkpos : 0 < n ^ k := Nat.pow_pos hn0
    calc 8 * n ^ k < 16 * n ^ k := by omega
      _ ≤ 2 ^ n * 2 ^ n * n ^ n := Nat.mul_le_mul h4n hnk
      _ ≤ 2 ^ n * 2 ^ n * (n ^ n * n ^ n) := by
          apply Nat.mul_le_mul_left
          exact Nat.le_mul_of_pos_right _ (Nat.pow_pos hn0)
  have h2 : 8 * 2 ^ n < (2 * n) ^ (2 * n) := by
    have e : (2 * n) ^ (2 * n) = (2 ^ n * 2 ^ n) * (n ^ n * n ^ n) := by ring
    rw [e]
    have h32 : 32 ≤ 2 ^ n := by
      calc 32 = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn5
    have h2pos : 0 < 2 ^ n := by positivity
    calc 8 * 2 ^ n < 32 * 2 ^ n := by omega
      _ ≤ 2 ^ n * 2 ^ n := Nat.mul_le_mul_right _ h32
      _ ≤ 2 ^ n * 2 ^ n * (n ^ n * n ^ n) := Nat.le_mul_of_pos_right _ hnn
  have h3 : 10 ^ 10 ≤ (2 * n) ^ (2 * n) := by
    calc 10 ^ 10 = (2 * 5) ^ (2 * 5) := by norm_num
      _ ≤ (2 * n) ^ (2 * 5) := Nat.pow_le_pow_left (by omega) _
      _ ≤ (2 * n) ^ (2 * n) := Nat.pow_le_pow_right (by omega) (by omega)
  exact ⟨hkn, hn5, by omega, by omega, by omega⟩

/-! ### The estimate (11) for `σ` -/

/-- (11): with `C = ψ_{M(x+1)}(n+1)`, `K = ψ_M(n−k+1)`, `L = ψ_{Mx}(k+1)`, the number
`σ = C/(KL)` satisfies `|σ − a| < (n/M)·a` and `σ > a/2`, where `a = (x+1)^n/x^k`. -/
theorem sigma_estimate {k n x M : ℕ} (hk : 1 ≤ k) (hkn : k < n) (hx : 1 ≤ x)
    (hM : 2 * n < M) (hM1 : 1 < M) (hMx : 1 < M * x) (hMx1 : 1 < M * (x + 1)) :
    let a : ℝ := ((x : ℝ) + 1) ^ n / (x : ℝ) ^ k
    |σ (ψ hMx1 (n + 1)) (ψ hM1 (n - k + 1)) (ψ hMx (k + 1)) - a| ≤ (n : ℝ) / M * a ∧
      a / 2 < σ (ψ hMx1 (n + 1)) (ψ hM1 (n - k + 1)) (ψ hMx (k + 1)) := by
  intro a
  have hn0 : 0 < n := by omega
  have hxR : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hMR : (2 * n : ℝ) < M := by exact_mod_cast hM
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM1
  have hM0 : (0 : ℝ) < M := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have ha : 0 < a := by positivity
  -- Lemma 2.1 bounds, cast to ℝ
  have hC_up : (ψ hMx1 (n + 1) : ℝ) ≤ (2 * (M * (x + 1)) : ℝ) ^ n := by
    have := ψ_succ_le_pow hMx1 n; exact_mod_cast this
  have hC_lo : ((2 * (M * (x + 1)) - 1 : ℕ) : ℝ) ^ n ≤ (ψ hMx1 (n + 1) : ℝ) := by
    have := pow_le_ψ_succ hMx1 n; exact_mod_cast this
  have hK_up : (ψ hM1 (n - k + 1) : ℝ) ≤ (2 * M : ℝ) ^ (n - k) := by
    have := ψ_succ_le_pow hM1 (n - k); exact_mod_cast this
  have hK_lo : ((2 * M - 1 : ℕ) : ℝ) ^ (n - k) ≤ (ψ hM1 (n - k + 1) : ℝ) := by
    have := pow_le_ψ_succ hM1 (n - k); exact_mod_cast this
  have hL_up : (ψ hMx (k + 1) : ℝ) ≤ (2 * (M * x) : ℝ) ^ k := by
    have := ψ_succ_le_pow hMx k; exact_mod_cast this
  have hL_lo : ((2 * (M * x) - 1 : ℕ) : ℝ) ^ k ≤ (ψ hMx (k + 1) : ℝ) := by
    have := pow_le_ψ_succ hMx k; exact_mod_cast this
  -- positivity of the Pell numbers
  have hKpos : (0 : ℝ) < ψ hM1 (n - k + 1) := by
    have := Nat.one_le_pow (n - k) (2 * M - 1) (by omega)
    have h' : ((2 * M - 1 : ℕ) : ℝ) ^ (n - k) ≥ 1 := by exact_mod_cast this
    linarith
  have hLpos : (0 : ℝ) < ψ hMx (k + 1) := by
    have := Nat.one_le_pow k (2 * (M * x) - 1) (by omega)
    have h' : ((2 * (M * x) - 1 : ℕ) : ℝ) ^ k ≥ 1 := by exact_mod_cast this
    linarith
  have hCpos : (0 : ℝ) < ψ hMx1 (n + 1) := by
    have := Nat.one_le_pow n (2 * (M * (x + 1)) - 1) (by omega)
    have h' : ((2 * (M * (x + 1)) - 1 : ℕ) : ℝ) ^ n ≥ 1 := by exact_mod_cast this
    linarith
  -- casts of the subtractions
  have hcM : ((2 * M - 1 : ℕ) : ℝ) = 2 * M - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcMx : ((2 * (M * x) - 1 : ℕ) : ℝ) = 2 * (M * x) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  have hcMx1 : ((2 * (M * (x + 1)) - 1 : ℕ) : ℝ) = 2 * (M * (x + 1)) - 1 := by
    rw [Nat.cast_sub (by omega)]; push_cast; ring
  rw [hcM] at hK_lo
  rw [hcMx] at hL_lo
  rw [hcMx1] at hC_lo
  have h2M1 : (0 : ℝ) < 2 * M - 1 := by linarith
  have hMxR : (2 : ℝ) ≤ M * x := by nlinarith
  have h2Mx1 : (0 : ℝ) < 2 * (M * x) - 1 := by linarith
  have hMx1R : (0 : ℝ) < 2 * (M * (x + 1)) := by positivity
  -- upper bound: σ ≤ a (2M/(2M-1))^n ≤ a (1 + n/M)
  have hup : σ (ψ hMx1 (n + 1)) (ψ hM1 (n - k + 1)) (ψ hMx (k + 1)) ≤ a * (1 + (n : ℝ) / M) := by
    have hden_lo : (2 * M - 1 : ℝ) ^ n * (x : ℝ) ^ k
        ≤ (ψ hM1 (n - k + 1) : ℝ) * ψ hMx (k + 1) := by
      have h1 : (2 * M - 1 : ℝ) ^ n * (x : ℝ) ^ k
          = (2 * M - 1 : ℝ) ^ (n - k) * ((2 * M - 1) * x) ^ k := by
        rw [mul_pow, ← mul_assoc, ← pow_add, Nat.sub_add_cancel hkn.le]
      have h2 : ((2 * M - 1) * x : ℝ) ^ k ≤ (2 * (M * x) - 1 : ℝ) ^ k := by
        apply pow_le_pow_left₀ (by positivity)
        nlinarith
      rw [h1]
      exact mul_le_mul hK_lo (h2.trans hL_lo) (by positivity) hKpos.le
    have hσ : σ (ψ hMx1 (n + 1)) (ψ hM1 (n - k + 1)) (ψ hMx (k + 1))
        ≤ (2 * (M * (x + 1)) : ℝ) ^ n / ((2 * M - 1 : ℝ) ^ n * (x : ℝ) ^ k) := by
      unfold σ
      apply div_le_div₀ (by positivity) hC_up (by positivity) hden_lo
    have hratio : (2 * (M * (x + 1)) : ℝ) ^ n / ((2 * M - 1 : ℝ) ^ n * (x : ℝ) ^ k)
        = a * ((2 * M : ℝ) / (2 * M - 1)) ^ n := by
      simp only [a]
      rw [div_pow, div_mul_div_comm]
      congr 1
      · simp only [mul_pow]; ring
      · ring
    have h31 : ((2 * M : ℝ) / (2 * M - 1)) ^ n ≤ 1 + 2 * n / (2 * M) :=
      lemma_3_1 (q := n) (by omega) (β := 2 * M) (by linarith)
    have h31' : ((2 * M : ℝ) / (2 * M - 1)) ^ n ≤ 1 + (n : ℝ) / M := by
      have : (2 * (n : ℝ) / (2 * M)) = n / M := by field_simp
      linarith
    calc σ (ψ hMx1 (n + 1)) (ψ hM1 (n - k + 1)) (ψ hMx (k + 1))
        ≤ a * ((2 * M : ℝ) / (2 * M - 1)) ^ n := hratio ▸ hσ
      _ ≤ a * (1 + (n : ℝ) / M) := mul_le_mul_of_nonneg_left h31' ha.le
  -- lower bound: σ ≥ a (1 - 1/(2M(x+1)))^n > a (1 - n/M)
  have hlo : a * (1 - (n : ℝ) / M) < σ (ψ hMx1 (n + 1)) (ψ hM1 (n - k + 1)) (ψ hMx (k + 1)) := by
    have hden_up : (ψ hM1 (n - k + 1) : ℝ) * ψ hMx (k + 1) ≤ (2 * M : ℝ) ^ n * (x : ℝ) ^ k := by
      have h1 : (2 * M : ℝ) ^ n * (x : ℝ) ^ k = (2 * M : ℝ) ^ (n - k) * (2 * (M * x) : ℝ) ^ k := by
        have e : (2 * M : ℝ) ^ n = (2 * M) ^ (n - k) * (2 * M) ^ k := by
          rw [← pow_add, Nat.sub_add_cancel hkn.le]
        rw [e]
        simp only [mul_pow]
        ring
      rw [h1]
      exact mul_le_mul hK_up hL_up hLpos.le (by positivity)
    have hσ : (2 * (M * (x + 1)) - 1 : ℝ) ^ n / ((2 * M : ℝ) ^ n * (x : ℝ) ^ k)
        ≤ σ (ψ hMx1 (n + 1)) (ψ hM1 (n - k + 1)) (ψ hMx (k + 1)) := by
      unfold σ
      apply div_le_div₀ hCpos.le hC_lo (by positivity) hden_up
    have hratio : (2 * (M * (x + 1)) - 1 : ℝ) ^ n / ((2 * M : ℝ) ^ n * (x : ℝ) ^ k)
        = a * (1 - 1 / (2 * M * (x + 1))) ^ n := by
      simp only [a]
      have e : (1 - 1 / (2 * M * (x + 1)) : ℝ) = (2 * (M * (x + 1)) - 1) / (2 * (M * (x + 1))) := by
        field_simp
      rw [e, div_pow, div_mul_div_comm, div_eq_div_iff (by positivity) (by positivity)]
      simp only [mul_pow]
      ring
    have h32 := lemma_3_2 (n := n) (M := M) hn0 (by omega) (x : ℝ) (by positivity)
    calc a * (1 - (n : ℝ) / M) < a * (1 - 1 / (2 * M * (x + 1))) ^ n :=
          mul_lt_mul_of_pos_left h32 ha
      _ = _ := hratio.symm
      _ ≤ _ := hσ
  have hnM : (n : ℝ) / M < 1 / 2 := by
    rw [div_lt_iff₀ hM0]; linarith
  constructor
  · rw [abs_le]
    constructor
    · have : a * (1 - (n : ℝ) / M) = a - n / M * a := by ring
      linarith
    · have : a * (1 + (n : ℝ) / M) = a + n / M * a := by ring
      linarith
  · have : a * (1 - (n : ℝ) / M) > a / 2 := by nlinarith
    linarith

end JSWW1976
