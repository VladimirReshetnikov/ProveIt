import Diophantine.Paper1976.MR
import Diophantine.Paper1976.Ineq

/-!
# Jones 1982, Lemmas 2.17–2.23: Pell sequences and the exponential relation

> **2.17.** For real `α` and `n ≥ 0`: if `α < 1` then `(1−α)ⁿ ≥ 1 − nα`; if `0 ≤ α ≤ 1/2`
> then `(1−α)⁻¹ ≤ 1 + 2α`.
> **Lemma 2.18.** `(A²−1)y² + 1 = □ ⟺ y = ψ_A(n)` for some `n`.
> **Lemma 2.19.** `(2A−1)ⁿ ≤ ψ_A(n+1) ≤ (2A)ⁿ`.
> **Lemma 2.20.** `ψ_A(n) ≡ n (mod A−1)`.
> **Lemma 2.21.** If `0 < V < A` then `A ≤ 2AV − V² − 1`.
> **Lemma 2.22.** For positive `V, B, W`: `W = V^B` iff there are positive `A, C` with
> (i) `V^(3B) < A`, (ii) `W³ < A`, (iii) `(V²−1)WC ≡ V(W²−1) (mod 2AV − V² − 1)`,
> (iv) `C = ψ_A(B)`.
> **Lemma 2.23.** If `C₁ > 0`, `0 < B₁ ≤ B < A` and `C = ψ_A(B)`, then `C₁ = ψ_A(B₁)` iff
> (i) `(A²−1)C₁² + 1 = □`, (ii) `C₁ ≡ B₁ (mod A−1)`, (iii) `C₁ ≤ C`.

Lemma 2.22 is cited from [8] (Jones 1979); it is proved here from the congruence
`χ_A(B) ≡ V^B + ψ_A(B)(A − V) (mod 2AV − V² − 1)` (Lemma 2.4 of the 1976 article,
`Diophantine.χ_modEq_pow`): with `x = V^B`, `J = 2AV − V² − 1` and the Pell equation one
gets `(V²−1)xC ≡ V(x²−1) (mod J)`; together with (iii) this gives
`J ∣ V(W − x)(Wx + 1)`, and `V ⊥ J`, `|(W − x)(Wx + 1)| < max(W, x)³ < A ≤ J` force `W = x`.
The remark after Lemma 2.28 (the congruence `D ≡ W + C(A − V)` with `D = χ_A(B)` in place of
(iii), used in Theorem 3 and in §5) is `lemma_2_22'`.
-/

namespace Jones1982

open Pell Diophantine JSWW1976

/-- 2.17, first inequality (Bernoulli): `1 − nα ≤ (1 − α)ⁿ` for `α ≤ 1`. -/
theorem ineq_2_17_a {α : ℝ} (hα : α ≤ 1) (n : ℕ) : 1 - n * α ≤ (1 - α) ^ n :=
  JSWW1976.lemma_2_7 hα n

/-- 2.17, second inequality: `(1 − α)⁻¹ ≤ 1 + 2α` for `0 ≤ α ≤ 1/2`. -/
theorem ineq_2_17_b {α : ℝ} (h0 : 0 ≤ α) (h1 : α ≤ 1 / 2) : (1 - α)⁻¹ ≤ 1 + 2 * α :=
  JSWW1976.lemma_2_8 h0 h1

/-- Lemma 2.18: `(A²−1)y² + 1 = □ ⟺ y = ψ_A(n)` for some `n`. -/
theorem lemma_2_18 {A : ℕ} (hA : 1 < A) (y : ℕ) :
    IsSquare ((A * A - 1) * y ^ 2 + 1) ↔ ∃ n, y = ψ hA n :=
  ⟨exists_eq_ψ_of_square hA, by rintro ⟨n, rfl⟩; exact square_of_ψ hA n⟩

/-- Lemma 2.19: `(2A−1)ⁿ ≤ ψ_A(n+1) ≤ (2A)ⁿ`. -/
theorem lemma_2_19 {A : ℕ} (hA : 1 < A) (n : ℕ) :
    (2 * A - 1) ^ n ≤ ψ hA (n + 1) ∧ ψ hA (n + 1) ≤ (2 * A) ^ n :=
  ⟨pow_le_ψ_succ hA n, ψ_succ_le_pow hA n⟩

/-- Lemma 2.20: `ψ_A(n) ≡ n (mod A−1)`. -/
theorem lemma_2_20 {A : ℕ} (hA : 1 < A) (n : ℕ) : ψ hA n ≡ n [MOD A - 1] := ψ_modEq hA n

/-- Lemma 2.21: if `0 < V < A` then `A ≤ 2AV − V² − 1` (in the form `A + V² + 1 ≤ 2AV`). -/
theorem lemma_2_21 {A V : ℕ} (hV : 0 < V) (hVA : V < A) : A + V * V + 1 ≤ 2 * A * V := by
  nlinarith

theorem lemma_2_21' {A V : ℕ} (hV : 0 < V) (hVA : V < A) : A ≤ 2 * A * V - V * V - 1 := by
  have := lemma_2_21 hV hVA; omega

/-! ### The basic congruence -/

/-- The modulus `J = 2AV − V² − 1` of Lemma 2.22, cast to `ℤ` (for `V ≤ A`, `0 < V`). -/
theorem J_cast {A V : ℕ} (hV : 0 < V) (hVA : V ≤ A) :
    ((2 * A * V - V * V - 1 : ℕ) : ℤ) = 2 * A * V - V * V - 1 := by
  have hmod : V * V + 1 ≤ 2 * A * V := by nlinarith
  have : V * V ≤ 2 * A * V - 1 := by omega
  push_cast [Nat.sub_sub, Nat.cast_sub hmod]
  ring

/-- With `x = V^B`, `C = ψ_A(B)`: `(V²−1) x C ≡ V (x² − 1) (mod 2AV − V² − 1)`, as a
divisibility in `ℤ`.  From `χ_A(B) ≡ x + C(A − V)` and the Pell equation. -/
theorem key_congruence {A V : ℕ} (hA : 1 < A) (hV : 0 < V) (hVA : V ≤ A) (B : ℕ) :
    ((2 * A * V - V * V - 1 : ℤ)) ∣
      ((V : ℤ) ^ 2 - 1) * (V : ℤ) ^ B * ψ hA B - V * (((V : ℤ) ^ B) ^ 2 - 1) := by
  have h1 := χ_modEq_pow hA hV hVA B
  rw [Nat.ModEq.comm, Nat.modEq_iff_dvd, J_cast hV hVA] at h1
  obtain ⟨k, hk⟩ := h1
  push_cast [Nat.cast_sub hVA] at hk
  have hD : (χ hA B : ℤ) ^ 2 = ((A : ℤ) ^ 2 - 1) * (ψ hA B : ℤ) ^ 2 + 1 := by
    have := χ_sq hA B
    have h' : ((χ hA B * χ hA B : ℕ) : ℤ) = (((A * A - 1) * ψ hA B * ψ hA B + 1 : ℕ) : ℤ) := by
      rw [this]
    push_cast [Nat.cast_sub (by nlinarith : 1 ≤ A * A)] at h'
    linear_combination h'
  -- `χ = x + C(A − V) + J k`
  have hχ : (χ hA B : ℤ) = (V : ℤ) ^ B + ψ hA B * (A - V) + (2 * A * V - V * V - 1) * k := by
    linear_combination hk
  rw [hχ] at hD
  refine ⟨(V : ℤ) ^ B * ψ hA B - V * (ψ hA B) ^ 2 +
    V * k * (2 * ((V : ℤ) ^ B + ψ hA B * (A - V)) + (2 * A * V - V * V - 1) * k), ?_⟩
  linear_combination (-(V : ℤ)) * hD

/-- `V` and `J = 2AV − V² − 1` are coprime (in `ℤ`). -/
theorem isCoprime_V_J (A V : ℤ) : IsCoprime V (2 * A * V - V * V - 1) :=
  ⟨2 * A - V, -1, by ring⟩

/-- The size estimate: for `1 ≤ W, x` with `W³ < A` and `x³ < A`, `|(W − x)(Wx + 1)| < A`. -/
theorem abs_mul_lt {W x A : ℕ} (hW : 1 ≤ W) (hx : 1 ≤ x) (hWA : W ^ 3 < A) (hxA : x ^ 3 < A) :
    |((W : ℤ) - x) * (W * x + 1)| < A := by
  rcases lt_trichotomy W x with h | h | h
  · have hWx : W + 1 ≤ x := h
    rw [abs_of_neg (by
      have : (W : ℤ) < x := by exact_mod_cast h
      have : (0 : ℤ) < W * x + 1 := by positivity
      nlinarith)]
    have hxA' : ((x : ℤ)) ^ 3 < A := by exact_mod_cast hxA
    have hWx' : (W : ℤ) + 1 ≤ x := by exact_mod_cast hWx
    have hW' : (1 : ℤ) ≤ W := by exact_mod_cast hW
    have e1 : (x : ℤ) ^ 2 * W ≤ x ^ 2 * (x - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    have e2 : (x : ℤ) ≤ W ^ 2 * x :=
      le_mul_of_one_le_left (by positivity) (by nlinarith)
    nlinarith [sq_nonneg (x : ℤ)]
  · subst h; simp; exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) hWA
  · have hxW : x + 1 ≤ W := h
    rw [abs_of_pos (by
      have : (x : ℤ) < W := by exact_mod_cast h
      have : (0 : ℤ) < W * x + 1 := by positivity
      nlinarith)]
    have hWA' : ((W : ℤ)) ^ 3 < A := by exact_mod_cast hWA
    have hxW' : (x : ℤ) + 1 ≤ W := by exact_mod_cast hxW
    have hx' : (1 : ℤ) ≤ x := by exact_mod_cast hx
    have e1 : (W : ℤ) ^ 2 * x ≤ W ^ 2 * (W - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg _)
    have e2 : (W : ℤ) ≤ x ^ 2 * W :=
      le_mul_of_one_le_left (by positivity) (by nlinarith)
    nlinarith [sq_nonneg (W : ℤ)]

/-! ### Lemma 2.22 -/

/-- Lemma 2.22, sufficiency: (i)–(iv) imply `W = V^B`. -/
theorem pow_of_congruence {A B C V W : ℕ} (hV : 0 < V) (hW : 0 < W) (hB : 0 < B)
    (hi : V ^ (3 * B) < A) (hii : W ^ 3 < A)
    (hiii : (V ^ 2 - 1) * W * C ≡ V * (W ^ 2 - 1) [MOD 2 * A * V - V * V - 1])
    (hiv : ∀ hA : 1 < A, C = ψ hA B) : W = V ^ B := by
  have hV3 : V ≤ V ^ (3 * B) := Nat.le_self_pow (by omega) V
  have hVA : V < A := by omega
  have hA : 1 < A := by omega
  have hC := hiv hA
  subst hC
  -- (iii) in `ℤ`
  have h3 : ((2 * A * V - V * V - 1 : ℤ)) ∣
      (V : ℤ) * ((W : ℤ) ^ 2 - 1) - ((V : ℤ) ^ 2 - 1) * W * ψ hA B := by
    have := hiii
    rw [Nat.modEq_iff_dvd, J_cast hV hVA.le] at this
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hV), Nat.cast_sub (Nat.one_le_pow _ _ hW)] at this
    exact this
  have hk := key_congruence hA hV hVA.le B
  -- combine: `J ∣ V (W − x)(Wx + 1)`
  have h4 : ((2 * A * V - V * V - 1 : ℤ)) ∣
      (V : ℤ) * (((W : ℤ) - V ^ B) * (W * V ^ B + 1)) := by
    have e : (V : ℤ) * (((W : ℤ) - V ^ B) * (W * V ^ B + 1)) =
        ((V : ℤ) * ((W : ℤ) ^ 2 - 1) - ((V : ℤ) ^ 2 - 1) * W * ψ hA B) * (V : ℤ) ^ B +
        (((V : ℤ) ^ 2 - 1) * (V : ℤ) ^ B * ψ hA B - V * (((V : ℤ) ^ B) ^ 2 - 1)) * W := by
      ring
    rw [e]
    exact dvd_add (dvd_mul_of_dvd_left h3 _) (dvd_mul_of_dvd_left hk _)
  have h5 : ((2 * A * V - V * V - 1 : ℤ)) ∣ ((W : ℤ) - V ^ B) * (W * V ^ B + 1) :=
    (isCoprime_V_J A V).symm.dvd_of_dvd_mul_left h4
  -- sizes
  have hx3 : (V ^ B) ^ 3 < A := by rw [← pow_mul, mul_comm]; exact hi
  have habs := abs_mul_lt (Nat.one_le_iff_ne_zero.2 hW.ne') (Nat.one_le_pow _ _ hV) hii hx3
  have hAJ : (A : ℤ) ≤ 2 * A * V - V * V - 1 := by
    have := lemma_2_21 hV hVA
    have h' : ((A + V * V + 1 : ℕ) : ℤ) ≤ ((2 * A * V : ℕ) : ℤ) := by exact_mod_cast this
    push_cast at h'
    linarith
  have h6 : ((W : ℤ) - V ^ B) * (W * V ^ B + 1) = 0 :=
    Int.eq_zero_of_abs_lt_dvd h5 (by push_cast at habs ⊢; linarith)
  rcases mul_eq_zero.1 h6 with h7 | h7
  · have : (W : ℤ) = (V : ℤ) ^ B := by linarith
    exact_mod_cast this
  · exfalso
    have : (0 : ℤ) < W * V ^ B + 1 := by positivity
    linarith

/-- The congruence (iii) of Lemma 2.22 holds for `W = V^B`, `C = ψ_A(B)` (any `A ≥ V`). -/
theorem lemma_2_22_iii {A V : ℕ} (hA : 1 < A) (hV : 0 < V) (hVA : V ≤ A) (B : ℕ) :
    (V ^ 2 - 1) * (V ^ B) * ψ hA B ≡ V * ((V ^ B) ^ 2 - 1) [MOD 2 * A * V - V * V - 1] := by
  rw [Nat.modEq_iff_dvd, J_cast hV hVA]
  have key := key_congruence hA hV hVA B
  have e : (((V * ((V ^ B) ^ 2 - 1) : ℕ) : ℤ) - (((V ^ 2 - 1) * V ^ B * ψ hA B : ℕ) : ℤ)) =
      -(((V : ℤ) ^ 2 - 1) * (V : ℤ) ^ B * ψ hA B - V * (((V : ℤ) ^ B) ^ 2 - 1)) := by
    push_cast [Nat.cast_sub (Nat.one_le_pow _ _ hV),
      Nat.cast_sub (Nat.one_le_pow _ _ (pow_pos hV B))]
    ring
  rw [e]
  exact key.neg_right

/-- Lemma 2.22, necessity: `W = V^B` satisfies (i)–(iv) with `A = 2V^(3B) + 1`, `C = ψ_A(B)`. -/
theorem exists_congruence_of_pow {B V : ℕ} (hV : 0 < V) (hB : 0 < B) :
    ∃ A C : ℕ, V ^ (3 * B) < A ∧ (V ^ B) ^ 3 < A ∧
      (V ^ 2 - 1) * (V ^ B) * C ≡ V * ((V ^ B) ^ 2 - 1) [MOD 2 * A * V - V * V - 1] ∧
      ∀ hA : 1 < A, C = ψ hA B := by
  have hA : 1 < 2 * V ^ (3 * B) + 1 := by
    have := Nat.one_le_pow (3 * B) V hV; omega
  have hV3 : V ≤ V ^ (3 * B) := Nat.le_self_pow (by omega) V
  exact ⟨2 * V ^ (3 * B) + 1, ψ hA B, by omega, by rw [← pow_mul, mul_comm]; omega,
    lemma_2_22_iii hA hV (by omega) B, fun _ => rfl⟩

/-- Lemma 2.22: for positive `V, B, W`, `W = V^B` iff there are `A, C` with
(i) `V^(3B) < A`, (ii) `W³ < A`, (iii) `(V²−1)WC ≡ V(W²−1) (mod 2AV − V² − 1)`,
(iv) `C = ψ_A(B)`. -/
theorem lemma_2_22 {B V W : ℕ} (hV : 0 < V) (hB : 0 < B) (hW : 0 < W) :
    W = V ^ B ↔ ∃ A C : ℕ, V ^ (3 * B) < A ∧ W ^ 3 < A ∧
      (V ^ 2 - 1) * W * C ≡ V * (W ^ 2 - 1) [MOD 2 * A * V - V * V - 1] ∧
      ∀ hA : 1 < A, C = ψ hA B := by
  constructor
  · rintro rfl; exact exists_congruence_of_pow hV hB
  · rintro ⟨A, C, hi, hii, hiii, hiv⟩
    exact pow_of_congruence hV hW hB hi hii hiii hiv

/-- The `χ`-form of Lemma 2.22, sufficiency: `V^(3B) < A`, `W³ < A` and
`χ_A(B) ≡ W + ψ_A(B)(A − V) (mod 2AV − V² − 1)` give `W = V^B`. -/
theorem pow_of_χ_congruence {A B V W : ℕ} (hV : 0 < V) (hB : 0 < B)
    (hi : V ^ (3 * B) < A) (hii : W ^ 3 < A) (hA : 1 < A)
    (hiii : χ hA B ≡ W + ψ hA B * (A - V) [MOD 2 * A * V - V * V - 1]) : W = V ^ B := by
  have hV3 : V ≤ V ^ (3 * B) := Nat.le_self_pow (by omega) V
  have hVA : V < A := by omega
  have h1 := χ_modEq_pow hA hV hVA.le B
  have h2 : W ≡ V ^ B [MOD 2 * A * V - V * V - 1] :=
    Nat.ModEq.add_right_cancel' _ (hiii.symm.trans h1)
  have hAJ := lemma_2_21' hV hVA
  have hx3 : (V ^ B) ^ 3 < A := by rw [← pow_mul, mul_comm]; exact hi
  have hWle : W ≤ W ^ 3 := Nat.le_self_pow (by norm_num) W
  have hxle : V ^ B ≤ (V ^ B) ^ 3 := Nat.le_self_pow (by norm_num) _
  exact Nat.ModEq.eq_of_lt_of_lt h2 (by omega) (by omega)

/-- The variant of Lemma 2.22 from the remark after Lemma 2.28 (used in Theorem 3 and §5):
with `D = χ_A(B)` available, (iii) may be replaced by `D ≡ W + C(A − V) (mod 2AV − V² − 1)`. -/
theorem lemma_2_22' {B V W : ℕ} (hV : 0 < V) (hB : 0 < B) (hW : 0 < W) :
    W = V ^ B ↔ ∃ A C D : ℕ, V ^ (3 * B) < A ∧ W ^ 3 < A ∧
      D ≡ W + C * (A - V) [MOD 2 * A * V - V * V - 1] ∧
      ∀ hA : 1 < A, C = ψ hA B ∧ D = χ hA B := by
  constructor
  · rintro rfl
    have hA : 1 < 2 * V ^ (3 * B) + 1 := by
      have := Nat.one_le_pow (3 * B) V hV; omega
    have hV3 : V ≤ V ^ (3 * B) := Nat.le_self_pow (by omega) V
    refine ⟨2 * V ^ (3 * B) + 1, ψ hA B, χ hA B, by omega, by rw [← pow_mul, mul_comm]; omega,
      ?_, fun _ => ⟨rfl, rfl⟩⟩
    exact χ_modEq_pow hA hV (by omega) B
  · rintro ⟨A, C, D, hi, hii, hiii, hiv⟩
    have hV3 : V ≤ V ^ (3 * B) := Nat.le_self_pow (by omega) V
    have hA : 1 < A := by omega
    obtain ⟨hC, hD⟩ := hiv hA
    subst hC hD
    exact pow_of_χ_congruence hV hB hi hii hA hiii

/-! ### Lemma 2.23 -/

/-- Lemma 2.23: for `C₁ > 0`, `0 < B₁ ≤ B < A` and `C = ψ_A(B)`, `C₁ = ψ_A(B₁)` iff
(i) `(A²−1)C₁² + 1 = □`, (ii) `C₁ ≡ B₁ (mod A−1)`, (iii) `C₁ ≤ C`. -/
theorem lemma_2_23 {A B B₁ C₁ : ℕ} (hA : 1 < A) (hC₁ : 0 < C₁) (hB₁ : 0 < B₁) (hB₁B : B₁ ≤ B)
    (hBA : B < A) :
    C₁ = ψ hA B₁ ↔
      IsSquare ((A * A - 1) * C₁ ^ 2 + 1) ∧ C₁ ≡ B₁ [MOD A - 1] ∧ C₁ ≤ ψ hA B := by
  constructor
  · rintro rfl
    exact ⟨square_of_ψ hA B₁, ψ_modEq hA B₁, (strictMono_y hA).monotone hB₁B⟩
  · rintro ⟨hi, hii, hiii⟩
    obtain ⟨t, rfl⟩ := exists_eq_ψ_of_square hA hi
    have ht : 0 < t := by
      by_contra h0
      push Not at h0
      have : t = 0 := by omega
      subst this
      simp [ψ] at hC₁
    have htB : t ≤ B := (strictMono_y hA).le_iff_le.1 hiii
    have h1 : t ≡ B₁ [MOD A - 1] := (ψ_modEq hA t).symm.trans hii
    obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
    obtain ⟨B₁', rfl⟩ : ∃ B₁', B₁ = B₁' + 1 := ⟨B₁ - 1, by omega⟩
    have h2 : t' ≡ B₁' [MOD A - 1] := Nat.ModEq.add_right_cancel' 1 h1
    have := Nat.ModEq.eq_of_lt_of_lt h2 (by omega) (by omega)
    rw [this]

end Jones1982
