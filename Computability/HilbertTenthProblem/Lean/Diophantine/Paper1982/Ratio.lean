import Diophantine.Paper1982.Exponential
import Diophantine.Paper1978.Lemma28
import Diophantine.Paper1978.Lemma210
import Diophantine.Paper1976.Theorem39b
import Diophantine.Paper1976.Ineq3

/-!
# Jones 1982, Lemmas 2.24, 2.25: `N² ∣ C(2R, R)` and `b pow 2` by the ratio method

> **Lemma 2.24.** For `1 ≤ U`, `1 ≤ R`: `(U+1)^(2R)/U^R = Σ_{i<R} C(2R,i)/U^(R−i) + C(2R,R)
> + Σ_{i>R} C(2R,i) U^(i−R)`, and the first sum is `< 2^(2R)/U`.
>
> **Lemma 2.25.** For `R ≥ 8`, `N ≥ 8`, `R ≥ b` and `N ≥ b > 0`, in order that `N² ∣ C(2R,R)`
> and `b pow 2` it is necessary and sufficient that there exist positive integers `h, s, w, φ`
> and integers `A, B', C, K, M, P, U, V, W, Y` satisfying
> (B1) `P = 2M²U`, (B2) `(P²−1)K² + 1 = □`, (B3) `((C/K) − Y)² < 1/4`,
> (B4) `K = R + 1 + h(P−1)`, (B5) `M = RY`, (B6) `A = M(U+1)`, (B7) `B' = 2R + 1`,
> (B8) `C = B' + φ`, (B9) `U = N²w`, (B10) `Y = N²s`, (B11) `W = bw`, (B12) `V = 2`,
> (B13) `(V²−1)WC ≡ V(W²−1) (mod 2AV − V² − 1)`, (B14) `C = ψ_A(B')`.
> Furthermore the initial conditions with (B5)–(B10), (B12) imply `1 < A`, `0 < B'`,
> `B' ≤ C`, `0 < V < A` and `0 < 2AV − V² − 1`.  Also (B8) may be replaced by (B8')
> `C = B' + W + φ`.

The main idea (the article's remark): `C/K = ψ_{M(U+1)}(2R+1)/ψ_{2M²U}(R+1)` is within
`2ρ·R/A` of `ρ = (U+1)^(2R)/U^R` (the real core `ratio_core`, from the bounds
`(2a)ⁿ(1 − n/(2a)) ≤ ψ_a(n+1) ≤ (2a)ⁿ` and the 1978 `core_estimate`), and `⌊ρ⌋ ≡ C(2R,R)
(mod U)` with fractional part `< 2^(2R)/U` (Lemma 2.24, from the 1976 `binomial_split`).
B3 (in the form `4(C − KY)² < K²`) then pins `Y` to `⌊ρ⌋`, once `U > 4·2^(2R)` is known
from `W = 2^(2R+1)` (Lemma 2.22 applied to B13, B14), which itself needs the sizes
`2^(6R+3) < A`, `W³ < A` obtained from the same estimate.

`B25core` collects (B1)–(B12), (B14); `lemma_2_25` adds (B13) and `lemma_2_25'` adds the
`χ`-form congruence `D ≡ W + C(A − V)` with `D² = (A²−1)C² + 1` (remark after Lemma 2.28, the
form used in Theorem 3 and in §5).
-/

namespace Jones1982

open Pell Diophantine JSWW1976 Jones1978

/-! ### Lemma 2.24 -/

/-- Lemma 2.24 in the form used: for `R ≥ 1` and `c·2^(2R) < U`,
`(U+1)^(2R) = Q U^R + v` with `c v < U^R` and `Q = C(2R,R) + w U`. -/
theorem lemma_2_24 {R U c : ℕ} (hR : 1 ≤ R) (hc : 0 < c) (hU : c * 2 ^ (2 * R) < U) :
    ∃ Q v w : ℕ, (U + 1) ^ (2 * R) = Q * U ^ R + v ∧ c * v < U ^ R ∧
      Q = (2 * R).choose R + w * U := by
  have hU1 : 1 ≤ U := by
    have : 1 ≤ c * 2 ^ (2 * R) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  obtain ⟨w, v, hsplit, hv, -⟩ :=
    binomial_split (n := 2 * R) (k := R) (x := U) (by omega) hU1
  refine ⟨w * U + (2 * R).choose R, v, w, ?_, ?_, by ring⟩
  · rw [hsplit]; ring
  · have h1 : c * v * U ≤ c * 2 ^ (2 * R) * U ^ R := by
      rw [mul_assoc, mul_assoc]; exact Nat.mul_le_mul_left c hv
    have h2 : c * 2 ^ (2 * R) * U ^ R < U * U ^ R :=
      Nat.mul_lt_mul_of_pos_right hU (by positivity)
    have h3 : c * v * U < U ^ R * U := by rw [mul_comm (U ^ R) U]; omega
    exact Nat.lt_of_mul_lt_mul_right h3

/-- The real form of Lemma 2.24: `(U+1)^(2R)/U^R = Q + f` with `0 ≤ f < 1/c` and
`Q = C(2R,R) + wU`. -/
theorem rho_split_c {R U c : ℕ} (hR : 1 ≤ R) (hc : 0 < c) (hU : c * 2 ^ (2 * R) < U) :
    ∃ (Q w : ℕ) (f : ℝ), 0 ≤ f ∧ f < 1 / c ∧ Q = (2 * R).choose R + w * U ∧
      ((U : ℝ) + 1) ^ (2 * R) / (U : ℝ) ^ R = Q + f := by
  obtain ⟨Q, v, w, hsplit, hv, hQ⟩ := lemma_2_24 hR hc hU
  have hU0 : 0 < U := by
    have : 1 ≤ c * 2 ^ (2 * R) := Nat.one_le_iff_ne_zero.2 (by positivity)
    omega
  have hUR : (0 : ℝ) < (U : ℝ) ^ R := by positivity
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  refine ⟨Q, w, (v : ℝ) / (U : ℝ) ^ R, by positivity, ?_, hQ, ?_⟩
  · rw [div_lt_div_iff₀ hUR hcR]
    have : (c * v : ℝ) < (U : ℝ) ^ R := by exact_mod_cast hv
    linarith
  · have hvR : ((U : ℝ) + 1) ^ (2 * R) = (Q : ℝ) * (U : ℝ) ^ R + v := by
      have := congrArg (fun m : ℕ => (m : ℝ)) hsplit
      push_cast at this ⊢
      exact this
    rw [hvR]
    field_simp

/-! ### The real core -/

/-- The main estimate: for `K = ψ_P(R+1)`, `C = ψ_A(2R+1)` with `A = M(U+1)`, `P = 2M²U`
and `ρ = (U+1)^(2R)/U^R`, `|C − Kρ| ≤ 2Kρ·(R/A)` (and `K > 0`), assuming `2R ≤ A`. -/
theorem ratio_core {R M U A P K C : ℕ} (hR : 1 ≤ R) (hU : 1 ≤ U)
    (hA : A = M * (U + 1)) (hP : P = 2 * M ^ 2 * U) (hA1 : 1 < A) (hP1 : 1 < P)
    (hK : K = ψ hP1 (R + 1)) (hC : C = ψ hA1 (2 * R + 1)) (h2R : 2 * R ≤ A) :
    0 < K ∧ |(C : ℝ) - K * (((U : ℝ) + 1) ^ (2 * R) / (U : ℝ) ^ R)| ≤
      2 * K * (((U : ℝ) + 1) ^ (2 * R) / (U : ℝ) ^ R) * ((R : ℝ) / A) := by
  have hKpos : 0 < K := by rw [hK]; exact ψ_pos_of_pos hP1 (by omega)
  refine ⟨hKpos, ?_⟩
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ((U : ℝ) + 1) ^ (2 * R) / (U : ℝ) ^ R := ⟨_, rfl⟩
  rw [← hρ]
  have hUR : (0 : ℝ) < (U : ℝ) ^ R := by positivity
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have hAR : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hε0 : (0 : ℝ) ≤ (R : ℝ) / A := by positivity
  have hε : (R : ℝ) / A ≤ 1 / 2 := by
    rw [div_le_iff₀ hAR]
    have : (2 * R : ℝ) ≤ A := by exact_mod_cast h2R
    linarith
  have hP0 : (0 : ℝ) < (2 * (P : ℝ)) ^ R := by positivity
  -- `(2P)^R ρ = (2A)^(2R)`
  have hid : (2 * (P : ℝ)) ^ R * ρ = (2 * (A : ℝ)) ^ (2 * R) := by
    have e1 : (2 * (P : ℝ)) ^ R = (2 * M) ^ (2 * R) * U ^ R := by
      rw [hP]; push_cast
      rw [show (2 * (2 * (M : ℝ) ^ 2 * U)) = (2 * M) ^ 2 * U by ring, mul_pow, ← pow_mul]
    have e2 : (2 * (A : ℝ)) ^ (2 * R) = (2 * M) ^ (2 * R) * (U + 1) ^ (2 * R) := by
      rw [hA]; push_cast
      rw [show (2 * ((M : ℝ) * (U + 1))) = (2 * M) * (U + 1) by ring, mul_pow]
    rw [e1, e2, hρ, mul_assoc, mul_div_cancel₀ _ hUR.ne']
  have hC1 : (2 * (P : ℝ)) ^ R * ρ * (1 - R / A) ≤ C := by
    rw [hid, hC]
    have := pow_mul_le_ψ_succ_real hA1 (2 * R)
    have e : ((2 * R : ℕ) : ℝ) / (2 * (A : ℝ)) = R / A := by
      push_cast; field_simp
    rw [e] at this
    exact this
  have hC2 : (C : ℝ) ≤ (2 * (P : ℝ)) ^ R * ρ := by
    rw [hid, hC]; exact ψ_succ_le_pow_real hA1 (2 * R)
  have hD1 : (2 * (P : ℝ)) ^ R * (1 - R / A) ≤ K := by
    rw [hK]
    have h1 := pow_mul_le_ψ_succ_real hP1 R
    have hA2P : (A : ℝ) ≤ 2 * P := by
      have : A ≤ 2 * P := by
        rw [hA, hP]
        have hM1 : 1 ≤ M := by
          by_contra h0; push Not at h0
          have : M = 0 := by omega
          rw [this] at hA; omega
        nlinarith
      exact_mod_cast this
    have h2 : (R : ℝ) / (2 * P) ≤ R / A :=
      div_le_div_of_nonneg_left (by positivity) hAR hA2P
    have h3 : (2 * (P : ℝ)) ^ R * (1 - R / A) ≤ (2 * (P : ℝ)) ^ R * (1 - R / (2 * P)) := by
      apply mul_le_mul_of_nonneg_left _ hP0.le; linarith
    exact h3.trans h1
  have hD2 : (K : ℝ) ≤ (2 * (P : ℝ)) ^ R := by rw [hK]; exact ψ_succ_le_pow_real hP1 R
  exact core_estimate hP0 hρ0 hε0 hε hC1 hC2 hD1 hD2

/-- B3 as a real inequality: `|C − KY| < K/2`. -/
theorem B3_real {C K Y : ℕ} (hK : 1 ≤ K) (B3 : 4 * ((C : ℤ) - K * Y) ^ 2 < (K : ℤ) ^ 2) :
    |(C : ℝ) - K * Y| < K / 2 := by
  have h1 : (4 * ((C : ℝ) - K * Y) ^ 2) < (K : ℝ) ^ 2 := by exact_mod_cast B3
  have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
  apply abs_lt_of_sq_lt_sq _ (by positivity)
  nlinarith

/-- From the estimate and B3: `U^(R−1) < Y` (the article's (3), (4)). -/
theorem Y_lower {C K Y U R : ℕ} {ρ ε : ℝ} (hK : 0 < K) (hU : 3 ≤ U) (hR : 1 ≤ R)
    (hρ : ρ = ((U : ℝ) + 1) ^ (2 * R) / (U : ℝ) ^ R) (hε0 : 0 ≤ ε) (hε : ε ≤ 1 / 4)
    (h1 : |(C : ℝ) - K * ρ| ≤ 2 * K * ρ * ε) (h2 : |(C : ℝ) - K * Y| < K / 2) :
    U ^ (R - 1) < Y := by
  have hUR0 : (0 : ℝ) < (U : ℝ) ^ R := by positivity
  have hρU : (U : ℝ) ^ R ≤ ρ := by
    rw [hρ, le_div_iff₀ hUR0]
    calc (U : ℝ) ^ R * (U : ℝ) ^ R = ((U : ℝ) ^ 2) ^ R := by ring
      _ ≤ ((U : ℝ) + 1) ^ (2 * R) := by
        rw [pow_mul]
        have hU0 : (0 : ℝ) ≤ U := by positivity
        exact pow_le_pow_left₀ (by positivity) (by nlinarith) R
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hρ0 : 0 ≤ ρ := by rw [hρ]; positivity
  have h3 : (K : ℝ) * ρ * (1 - 2 * ε) ≤ C := by
    have := (abs_le.1 h1).1; nlinarith
  have h4 : (C : ℝ) - K / 2 < K * Y := by
    have := (abs_lt.1 h2).2; linarith
  have h3' : (K : ℝ) * ρ / 2 ≤ C := by
    have : 0 ≤ (K : ℝ) * ρ * (1 / 2 - 2 * ε) :=
      mul_nonneg (mul_nonneg hKR.le hρ0) (by linarith)
    nlinarith
  have h5 : (K : ℝ) * (ρ / 2 - 1 / 2) < K * Y := by nlinarith
  have h6 : ρ / 2 - 1 / 2 < Y := lt_of_mul_lt_mul_left h5 hKR.le
  have h7 : (U : ℝ) ^ R = (U : ℝ) ^ (R - 1) * U := by
    rw [← pow_succ]; congr 1; omega
  have hU' : (3 : ℝ) ≤ U := by exact_mod_cast hU
  have h8 : (1 : ℝ) ≤ (U : ℝ) ^ (R - 1) := one_le_pow₀ (by linarith)
  have h9 : ((U : ℝ) ^ (R - 1) : ℝ) < Y := by nlinarith
  exact_mod_cast h9

/-- B2, B4 and B3 force the index of `K` to be `R + 1`. -/
theorem K_index {R A P K C Y : ℕ} (hA1 : 1 < A) (hP1 : 1 < P) (hR : 1 ≤ R) (hY : 1 ≤ Y)
    (hRP : R + 1 < P - 1) (hP3R : 3 * R + 1 ≤ P) (h4A : 4 * A ≤ P * P)
    (hC : C = ψ hA1 (2 * R + 1)) (B2 : IsSquare ((P ^ 2 - 1) * K ^ 2 + 1))
    (B4 : ∃ h, K = R + 1 + h * (P - 1)) (hK : 1 ≤ K)
    (B3 : 4 * ((C : ℤ) - K * Y) ^ 2 < (K : ℤ) ^ 2) :
    K = ψ hP1 (R + 1) := by
  obtain ⟨t, ht⟩ := exists_eq_ψ_of_square hP1 (by rw [← sq]; exact B2)
  obtain ⟨h, hh⟩ := B4
  have hmod : ψ hP1 t ≡ R + 1 [MOD P - 1] := by
    rw [← ht, hh]
    exact ((Nat.modEq_iff_dvd' (by omega)).2 ⟨h, by rw [Nat.add_sub_cancel_left, mul_comm]⟩).symm
  obtain ⟨p', hp'⟩ := index_eq_of_modEq hP1 hRP hmod
  rcases Nat.eq_zero_or_pos p' with hp0 | hp0
  · rw [ht, hp', hp0]; simp
  · exfalso
    have hκ : 2 * (2 * R) + 1 ≤ t := by
      rw [hp']
      have : P - 1 ≤ p' * (P - 1) := Nat.le_mul_of_pos_left _ hp0
      omega
    have h2C : 2 * C < K := by
      rw [hC, ht]; exact two_ψ_lt hA1 hP1 (by omega) h4A hκ
    have hB3 := B3_real hK B3
    have hY' : (1 : ℝ) ≤ Y := by exact_mod_cast hY
    have h2C' : (2 * C : ℝ) < K := by exact_mod_cast h2C
    have := (abs_lt.1 hB3).1
    nlinarith

/-! ### The conditions (B1)–(B12), (B14) -/

/-- Conditions (B1)–(B12) and (B14) of Lemma 2.25 (B3 in the form `4(C − KY)² < K²`). -/
structure B25core (R N b h s w φ A B' C K M P U V W Y : ℕ) : Prop where
  B1 : P = 2 * M ^ 2 * U
  B2 : IsSquare ((P ^ 2 - 1) * K ^ 2 + 1)
  B3 : 4 * ((C : ℤ) - K * Y) ^ 2 < (K : ℤ) ^ 2
  B4 : K = R + 1 + h * (P - 1)
  B5 : M = R * Y
  B6 : A = M * (U + 1)
  B7 : B' = 2 * R + 1
  B8 : C = B' + φ
  B9 : U = N ^ 2 * w
  B10 : Y = N ^ 2 * s
  B11 : W = b * w
  B12 : V = 2
  B14 : ∀ hA : 1 < A, C = ψ hA B'

/-- The sizes implied by the initial conditions and (B5)–(B10), (B12): `1 < A`, `0 < B'`,
`B' ≤ C`, `0 < V < A`, `0 < 2AV − V² − 1` (and `64 ≤ U`, `64 ≤ Y`, `512 ≤ M`,
`33280 ≤ A`). -/
theorem B25core.sizes {R N b h s w φ A B' C K M P U V W Y : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hs : 0 < s) (hw : 0 < w)
    (hB : B25core R N b h s w φ A B' C K M P U V W Y) :
    64 ≤ U ∧ 64 ≤ Y ∧ 512 ≤ M ∧ 33280 ≤ A ∧ 1 < A ∧ 0 < B' ∧ B' ≤ C ∧ 0 < V ∧ V < A ∧
      0 < 2 * A * V - V * V - 1 := by
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B14⟩ := hB
  subst B12
  have hN2 : 64 ≤ N ^ 2 := by nlinarith
  have hU : 64 ≤ U := by rw [B9]; nlinarith
  have hY : 64 ≤ Y := by rw [B10]; nlinarith
  have hM : 512 ≤ M := by rw [B5]; nlinarith
  have hA : 33280 ≤ A := by rw [B6]; nlinarith
  refine ⟨hU, hY, hM, hA, by omega, by omega, by omega, by omega, by omega, by omega⟩

set_option maxHeartbeats 1000000 in
/-- The sufficiency part of Lemma 2.25, first half: `K = ψ_P(R+1)`, `U^(R−1) < Y` and the
sizes `2^(6R+3) < A`, `W³ < A` (the article's (3)–(6)). -/
theorem B25core.core {R N b h s w φ A B' C K M P U V W Y : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbN : b ≤ N) (hs : 0 < s) (hw : 0 < w)
    (hB : B25core R N b h s w φ A B' C K M P U V W Y) :
    ∃ (hA1 : 1 < A) (hP1 : 1 < P), C = ψ hA1 (2 * R + 1) ∧ K = ψ hP1 (R + 1) ∧
      U ^ (R - 1) < Y ∧ R * U ^ R < A ∧ 2 ^ (6 * R + 3) < A ∧ W ^ 3 < A := by
  obtain ⟨hU64, hY64, hM512, hA33, hA1, -, -, -, -, -⟩ := hB.sizes hR hN hs hw
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B14⟩ := hB
  have hC : C = ψ hA1 (2 * R + 1) := by rw [B14 hA1, B7]
  -- sizes of `P`
  have hM2 : M ≤ M ^ 2 := Nat.le_self_pow two_ne_zero M
  have hP2M : 2 * M ^ 2 ≤ P := by rw [B1]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hMR : 64 * R ≤ M := by
    rw [B5]
    calc 64 * R = R * 64 := mul_comm _ _
      _ ≤ R * Y := Nat.mul_le_mul_left R hY64
  have hMA : M ≤ A := by rw [B6]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hP1 : 1 < P := by omega
  have hRP : R + 1 < P - 1 := by omega
  have hP3R : 3 * R + 1 ≤ P := by omega
  have h4A : 4 * A ≤ P * P := by
    rw [B6, B1]
    have h8 : 8 ≤ M ^ 3 := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ M ^ 3 := Nat.pow_le_pow_left (by omega) 3
    have e1 : M * 8 ≤ M ^ 4 := by
      calc M * 8 ≤ M * M ^ 3 := Nat.mul_le_mul_left _ h8
        _ = M ^ 4 := by ring
    have hU1 : 1 ≤ U := by omega
    calc 4 * (M * (U + 1)) ≤ 4 * (M * (2 * U)) := by
          apply Nat.mul_le_mul_left; apply Nat.mul_le_mul_left; omega
      _ = M * 8 * U := by ring
      _ ≤ M ^ 4 * U := Nat.mul_le_mul_right _ e1
      _ ≤ M ^ 4 * (U * U) := Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ hU1)
      _ ≤ 4 * (M ^ 4 * (U * U)) := Nat.le_mul_of_pos_left _ (by norm_num)
      _ = 2 * M ^ 2 * U * (2 * M ^ 2 * U) := by ring
  have hK1 : 1 ≤ K := by omega
  have hKψ : K = ψ hP1 (R + 1) :=
    K_index hA1 hP1 (by omega) (by omega) hRP hP3R h4A hC B2 ⟨h, B4⟩ hK1 B3
  refine ⟨hA1, hP1, hC, hKψ, ?_⟩
  -- the estimate
  obtain ⟨hKpos, hest⟩ := ratio_core (R := R) (M := M) (U := U) (by omega) (by omega) B6 B1 hA1
    hP1 hKψ hC (by omega)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ((U : ℝ) + 1) ^ (2 * R) / (U : ℝ) ^ R := ⟨_, rfl⟩
  rw [← hρ] at hest
  have hAR : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hAeq : (A : ℝ) = R * Y * (U + 1) := by rw [B6, B5]; push_cast; ring
  have hε0 : (0 : ℝ) ≤ (R : ℝ) / A := by positivity
  have hε65 : (R : ℝ) / A ≤ 1 / 65 := by
    rw [div_le_iff₀ hAR, hAeq]
    have hY' : (64 : ℝ) ≤ Y := by exact_mod_cast hY64
    have hU' : (64 : ℝ) ≤ U := by exact_mod_cast hU64
    have hR' : (0 : ℝ) ≤ R := by positivity
    have h1 : (R : ℝ) * 64 * 65 ≤ R * Y * (U + 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hY' hR') (by linarith) (by norm_num) (by positivity)
    linarith
  have hB3 := B3_real hK1 B3
  have hUY : U ^ (R - 1) < Y :=
    Y_lower hKpos (by omega) (by omega) hρ hε0 (by linarith) hest hB3
  -- (5), (6)
  have hUR : U ^ R = U ^ (R - 1) * U := by rw [← pow_succ]; congr 1; omega
  have hRU : R * U ^ R < A := by
    rw [B6, B5, hUR]
    have h1 : U ^ (R - 1) + 1 ≤ Y := hUY
    have h2 : R * (U ^ (R - 1) + 1) * (U + 1) ≤ R * Y * (U + 1) := by
      apply Nat.mul_le_mul_right; exact Nat.mul_le_mul_left _ h1
    have h3 : R * (U ^ (R - 1) + 1) * (U + 1) =
        R * (U ^ (R - 1) * U) + (R * U ^ (R - 1) + R * U + R) := by ring
    omega
  have hN2U : N ^ 2 ≤ U := by rw [B9]; exact Nat.le_mul_of_pos_right _ hw
  have h6R3 : 2 ^ (6 * R + 3) < A := by
    have h1 : 2 ^ (6 * R + 3) = 8 * (64 : ℕ) ^ R := by
      rw [pow_add, pow_mul, mul_comm]; norm_num
    have hN2 : 64 ≤ N ^ 2 := by
      calc 64 = 8 * 8 := by norm_num
        _ ≤ N * N := Nat.mul_le_mul hN hN
        _ = N ^ 2 := (sq N).symm
    have h2 : (64 : ℕ) ^ R ≤ (N ^ 2) ^ R := Nat.pow_le_pow_left hN2 R
    have h3 : (N ^ 2) ^ R ≤ U ^ R := Nat.pow_le_pow_left hN2U R
    have h4 : 8 * U ^ R ≤ R * U ^ R := Nat.mul_le_mul_right _ hR
    rw [h1]
    calc 8 * (64 : ℕ) ^ R ≤ 8 * U ^ R := by
          apply Nat.mul_le_mul_left; exact h2.trans h3
      _ ≤ R * U ^ R := h4
      _ < A := hRU
  have hWU : W ≤ U := by
    rw [B11, B9]
    apply Nat.mul_le_mul_right
    calc b ≤ N := hbN
      _ ≤ N ^ 2 := Nat.le_self_pow two_ne_zero N
  have hW3 : W ^ 3 < A := by
    have h1 : W ^ 3 ≤ U ^ 3 := Nat.pow_le_pow_left hWU 3
    have h2 : U ^ 3 ≤ U ^ R := Nat.pow_le_pow_right (by omega) (by omega)
    have h3 : U ^ R ≤ R * U ^ R := Nat.le_mul_of_pos_left _ (by omega)
    omega
  exact ⟨hUY, hRU, h6R3, hW3⟩

set_option maxHeartbeats 1000000 in
/-- The sufficiency part of Lemma 2.25, second half: given `W = 2^(2R+1)` (from Lemma 2.22),
`N² ∣ C(2R,R)` and `b pow 2` (the article's (7)–(9) and the conclusion). -/
theorem B25core.dvd {R N b h s w φ A B' C K M P U V W Y : ℕ}
    (hR : 8 ≤ R) (hN : 8 ≤ N) (hbN : b ≤ N) (hs : 0 < s) (hw : 0 < w)
    (hB : B25core R N b h s w φ A B' C K M P U V W Y) (hW : W = 2 ^ (2 * R + 1)) :
    N ^ 2 ∣ (2 * R).choose R ∧ ∃ k, b = 2 ^ k := by
  obtain ⟨hU64, hY64, hM512, hA33, -, -, -, -, -, -⟩ := hB.sizes hR hN hs hw
  obtain ⟨hA1, hP1, hC, hKψ, hUY, hRU, h6R3, hW3⟩ := hB.core hR hN hbN hs hw
  obtain ⟨B1, B2, B3, B4, B5, B6, B7, B8, B9, B10, B11, B12, B14⟩ := hB
  have hK1 : 1 ≤ K := by omega
  -- `b pow 2`
  have hbpow : ∃ k, b = 2 ^ k := by
    have hdvd : b ∣ 2 ^ (2 * R + 1) := ⟨w, by rw [← hW, B11]⟩
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨k, hk⟩
  refine ⟨?_, hbpow⟩
  have hMR : 64 * R ≤ M := by
    rw [B5]
    calc 64 * R = R * 64 := mul_comm _ _
      _ ≤ R * Y := Nat.mul_le_mul_left R hY64
  have hMA : M ≤ A := by rw [B6]; exact Nat.le_mul_of_pos_right _ (by omega)
  -- the estimate
  obtain ⟨hKpos, hest⟩ := ratio_core (R := R) (M := M) (U := U) (by omega) (by omega) B6 B1 hA1
    hP1 hKψ hC (by omega)
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = ((U : ℝ) + 1) ^ (2 * R) / (U : ℝ) ^ R := ⟨_, rfl⟩
  rw [← hρ] at hest
  have hAR : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
  have hAeq : (A : ℝ) = R * Y * (U + 1) := by rw [B6, B5]; push_cast; ring
  have hε0 : (0 : ℝ) ≤ (R : ℝ) / A := by positivity
  have hε65 : (R : ℝ) / A ≤ 1 / 65 := by
    rw [div_le_iff₀ hAR, hAeq]
    have hY' : (64 : ℝ) ≤ Y := by exact_mod_cast hY64
    have hU' : (64 : ℝ) ≤ U := by exact_mod_cast hU64
    have hR' : (0 : ℝ) ≤ R := by positivity
    have h1 : (R : ℝ) * 64 * 65 ≤ R * Y * (U + 1) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hY' hR') (by linarith) (by norm_num) (by positivity)
    linarith
  have hB3 := B3_real hK1 B3
  -- (7): `U > 4·2^(2R)`
  have hU4 : 4 * 2 ^ (2 * R) < U := by
    have h1 : 8 * W ≤ U := by
      rw [B11, B9]
      have : 8 * b ≤ N ^ 2 := by
        calc 8 * b ≤ N * N := Nat.mul_le_mul hN hbN
          _ = N ^ 2 := (sq N).symm
      calc 8 * (b * w) = (8 * b) * w := by ring
        _ ≤ N ^ 2 * w := Nat.mul_le_mul_right _ this
    have h2 : W = 2 * 2 ^ (2 * R) := by rw [hW, pow_succ]; ring
    have h3 : 0 < 2 ^ (2 * R) := by positivity
    omega
  obtain ⟨Q, w', f, hf0, hf4, hQ, hρQ⟩ := rho_split_c (c := 4) (by omega) (by norm_num) hU4
  rw [← hρ] at hρQ
  have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
  have hYε : 2 * (Y : ℝ) * ((R : ℝ) / A) ≤ 1 / 8 := by
    have hY' : (0 : ℝ) < Y := by exact_mod_cast (by omega : 0 < Y)
    have hR' : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
    have hU' : (64 : ℝ) ≤ U := by exact_mod_cast hU64
    have e : 2 * (Y : ℝ) * ((R : ℝ) / A) = 2 / (U + 1) := by
      rw [hAeq]; field_simp
    rw [e, div_le_iff₀ (by linarith)]
    linarith
  have hQY := nearest_of_estimate (Y := (Y : ℝ)) (Q := (Q : ℝ)) (f := f) (ε := (R : ℝ) / A) hKR
    (by exact_mod_cast (by omega : 1 ≤ Y)) hf0 (by linarith) (by positivity) hε0 (by linarith)
    hYε (by rw [← hρQ]; exact hest) hB3
  have hQY' : Q = Y := by
    have h1 : (Q : ℝ) < Y + 1 := by linarith [hQY.2]
    have h2 : (Y : ℝ) < Q + 1 := by linarith [hQY.1]
    have h1' : Q < Y + 1 := by exact_mod_cast h1
    have h2' : Y < Q + 1 := by exact_mod_cast h2
    omega
  -- `N² ∣ Y = C(2R,R) + w'U` and `N² ∣ U`
  have hN2Y : N ^ 2 ∣ Q := by rw [hQY', B10]; exact dvd_mul_right _ _
  have hN2U' : N ^ 2 ∣ w' * U := by rw [B9]; exact ⟨w' * w, by ring⟩
  rw [hQ] at hN2Y
  exact (Nat.dvd_add_left hN2U').1 hN2Y

/-! ### Necessity -/

set_option maxHeartbeats 1000000 in
/-- The necessity part of Lemma 2.25: from `N² ∣ C(2R,R)` and `b pow 2` all the quantities of
(B1)–(B12), (B14) can be found, with `W = 2^(2R+1)` and `B' + W < C` (so that (B8') is also
satisfiable). -/
theorem exists_B25core {R N b : ℕ} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) (hdvd : N ^ 2 ∣ (2 * R).choose R) (hpow : ∃ k, b = 2 ^ k) :
    ∃ h s w φ A B' C K M P U V W Y : ℕ, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < φ ∧
      B25core R N b h s w φ A B' C K M P U V W Y ∧ W = 2 ^ (2 * R + 1) ∧ B' + W < C ∧
      4096 * ((C : ℤ) - K * Y) ^ 2 ≤ 625 * (K : ℤ) ^ 2 := by
  obtain ⟨k, hk⟩ := hpow
  have hkR : k < 2 * R + 1 := by
    have : k < 2 ^ k := Nat.lt_two_pow_self
    omega
  obtain ⟨w, hw⟩ : ∃ w, w = 2 ^ (2 * R + 1 - k) := ⟨_, rfl⟩
  have hw0 : 0 < w := by rw [hw]; positivity
  have hbw : b * w = 2 ^ (2 * R + 1) := by
    rw [hk, hw, ← pow_add]; congr 1; omega
  obtain ⟨U, hU⟩ : ∃ U, U = N ^ 2 * w := ⟨_, rfl⟩
  have hN2 : 64 ≤ N ^ 2 := by nlinarith
  have hU64 : 64 ≤ U := by rw [hU]; nlinarith
  have hU8 : 8 * 2 ^ (2 * R) < U := by
    have h1 : 8 * (b * w) ≤ U := by
      rw [hU]
      have : 8 * b ≤ N ^ 2 := by nlinarith
      calc 8 * (b * w) = (8 * b) * w := by ring
        _ ≤ N ^ 2 * w := Nat.mul_le_mul_right _ this
    rw [hbw, pow_succ] at h1
    have : 0 < 2 ^ (2 * R) := by positivity
    omega
  -- `Y = ⌊ρ⌋`
  obtain ⟨Q, w', f, hf0, hf8, hQ, hρQ⟩ := rho_split_c (c := 8) (by omega) (by norm_num) hU8
  have hQpos : 0 < Q := by
    rw [hQ]; have := Nat.choose_pos (show R ≤ 2 * R by omega); omega
  have hN2Q : N ^ 2 ∣ Q := by
    rw [hQ]; exact dvd_add hdvd (by rw [hU]; exact ⟨w' * w, by ring⟩)
  obtain ⟨s, hs⟩ := hN2Q
  have hs0 : 0 < s := by
    by_contra h0; push Not at h0
    have : s = 0 := by omega
    rw [this] at hs; omega
  have hQ2R : 2 * R ≤ Q := by
    rw [hQ]
    have := JSWW1976.le_choose_of_lt (n := 2 * R) (k := R) (by omega) (by omega)
    omega
  obtain ⟨M, hM⟩ : ∃ M, M = R * Q := ⟨_, rfl⟩
  obtain ⟨A, hA⟩ : ∃ A, A = M * (U + 1) := ⟨_, rfl⟩
  have hMR16 : 16 * R ≤ M := by
    rw [hM]
    calc 16 * R = R * 16 := mul_comm _ _
      _ ≤ R * Q := Nat.mul_le_mul_left R (by omega)
  have hM8 : 8 ≤ M := by omega
  have hAM : M ≤ A := by rw [hA]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hA1 : 1 < A := by omega
  obtain ⟨P, hP⟩ : ∃ P, P = 2 * M ^ 2 * U := ⟨_, rfl⟩
  have hPM : M ≤ P := by
    rw [hP]
    calc M ≤ M ^ 2 := Nat.le_self_pow two_ne_zero M
      _ ≤ 2 * M ^ 2 * U := by
        have : 1 ≤ 2 * U := by omega
        calc M ^ 2 = M ^ 2 * 1 := (mul_one _).symm
          _ ≤ M ^ 2 * (2 * U) := Nat.mul_le_mul_left _ this
          _ = 2 * M ^ 2 * U := by ring
  have hP1 : 1 < P := by omega
  obtain ⟨C, hC⟩ : ∃ C, C = ψ hA1 (2 * R + 1) := ⟨_, rfl⟩
  obtain ⟨K, hK⟩ : ∃ K, K = ψ hP1 (R + 1) := ⟨_, rfl⟩
  -- B4: `K = R + 1 + h(P − 1)` with `h ≥ 1`
  have hKR1 : R + 1 ≤ K := by rw [hK]; exact yn_ge_n hP1 _
  have hKbig : 2 * P - 1 ≤ K := by
    rw [hK]
    calc 2 * P - 1 = (2 * P - 1) ^ 1 := (pow_one _).symm
      _ ≤ (2 * P - 1) ^ R := Nat.pow_le_pow_right (by omega) (by omega)
      _ ≤ ψ hP1 (R + 1) := pow_le_ψ_succ hP1 R
  have hKmod : K ≡ R + 1 [MOD P - 1] := by rw [hK]; exact ψ_modEq hP1 _
  obtain ⟨h, hh⟩ := (Nat.modEq_iff_dvd' hKR1).1 hKmod.symm
  have hh0 : 0 < h := by
    by_contra h0; push Not at h0
    have : h = 0 := by omega
    rw [this, mul_zero] at hh
    omega
  -- B8: `C > B' + W`
  have hCbig : 2 * R + 1 + 2 ^ (2 * R + 1) < C := by
    have h1 : 2 * A - 1 ≤ C := by
      rw [hC]
      calc 2 * A - 1 = (2 * A - 1) ^ 1 := (pow_one _).symm
        _ ≤ (2 * A - 1) ^ (2 * R) := Nat.pow_le_pow_right (by omega) (by omega)
        _ ≤ ψ hA1 (2 * R + 1) := pow_le_ψ_succ hA1 (2 * R)
    have h2 : U + 1 ≤ A := by rw [hA]; exact Nat.le_mul_of_pos_left _ (by omega)
    have h3 : 2 * R + 1 ≤ 2 ^ (2 * R) := by
      have := Nat.lt_two_pow_self (n := 2 * R); omega
    have h4 : 2 ^ (2 * R + 1) = 2 * 2 ^ (2 * R) := by rw [pow_succ]; ring
    omega
  -- B3 from the estimate
  obtain ⟨hKpos, hest⟩ := ratio_core (R := R) (M := M) (U := U) (by omega) (by omega) hA hP hA1
    hP1 hK hC (by omega)
  have hB3s : 4096 * ((C : ℤ) - K * Q) ^ 2 ≤ 625 * (K : ℤ) ^ 2 := by
    have hKR : (0 : ℝ) < K := by exact_mod_cast hKpos
    have hAR : (0 : ℝ) < A := by exact_mod_cast (by omega : 0 < A)
    have hAeq : (A : ℝ) = R * Q * (U + 1) := by rw [hA, hM]; push_cast; ring
    have hε0 : (0 : ℝ) ≤ (R : ℝ) / A := by positivity
    have hε32 : (R : ℝ) / A ≤ 1 / 32 := by
      rw [div_le_iff₀ hAR, hAeq]
      have hQ' : (1 : ℝ) ≤ Q := by exact_mod_cast hQpos
      have hU' : (64 : ℝ) ≤ U := by exact_mod_cast hU64
      have hR' : (0 : ℝ) ≤ R := by positivity
      have h1 : (R : ℝ) * 1 * 65 ≤ R * Q * (U + 1) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hQ' hR') (by linarith) (by norm_num) (by positivity)
      linarith
    have hYε : 2 * (Q : ℝ) * ((R : ℝ) / A) ≤ 1 / 8 := by
      have hQ' : (0 : ℝ) < Q := by exact_mod_cast hQpos
      have hR' : (0 : ℝ) < R := by exact_mod_cast (by omega : 0 < R)
      have hU' : (64 : ℝ) ≤ U := by exact_mod_cast hU64
      have e : 2 * (Q : ℝ) * ((R : ℝ) / A) = 2 / (U + 1) := by
        rw [hAeq]; field_simp
      rw [e, div_le_iff₀ (by linarith)]
      linarith
    have h1 := estimate_of_floor (Y := (Q : ℝ)) (f := f) (ε := (R : ℝ) / A) hKR
      (by exact_mod_cast hQpos) hf0 (by linarith) hε0 hε32 hYε (by rw [← hρQ]; exact hest)
    have h2 : |(C : ℝ) - K * Q| ^ 2 ≤ (25 / 64 * K) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [sq_abs] at h2
    have h3 : 4096 * ((C : ℝ) - K * Q) ^ 2 ≤ 625 * (K : ℝ) ^ 2 := by nlinarith
    exact_mod_cast h3
  have hB3 : 4 * ((C : ℤ) - K * Q) ^ 2 < (K : ℤ) ^ 2 := by
    have hK0 : (0 : ℤ) < K := by exact_mod_cast hKpos
    nlinarith
  refine ⟨h, s, w, C - (2 * R + 1), A, 2 * R + 1, C, K, M, P, U, 2, b * w, Q, hh0, hs0, hw0,
    by omega,
    ⟨hP, ?_, hB3, by rw [mul_comm]; omega, hM, hA, rfl, by omega, hU, hs, rfl, rfl, fun _ => hC⟩,
    hbw, by rw [hbw]; exact hCbig, hB3s⟩
  rw [hK, sq]; exact square_of_ψ hP1 _

/-! ### Lemma 2.25 -/

/-- Lemma 2.25 (with (B13) as printed). -/
theorem lemma_2_25 {R N b : ℕ} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) :
    (N ^ 2 ∣ (2 * R).choose R ∧ ∃ k, b = 2 ^ k) ↔
      ∃ h s w φ A B' C K M P U V W Y : ℕ, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < φ ∧
        B25core R N b h s w φ A B' C K M P U V W Y ∧
        (V ^ 2 - 1) * W * C ≡ V * (W ^ 2 - 1) [MOD 2 * A * V - V * V - 1] := by
  constructor
  · rintro ⟨hdvd, hpow⟩
    obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, hh, hs, hw, hφ, hB, hW, -⟩ :=
      exists_B25core hR hN hbR hb hbN hdvd hpow
    refine ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, hh, hs, hw, hφ, hB, ?_⟩
    obtain ⟨-, -, -, -, hA1, -, -, -, hVA, -⟩ := hB.sizes hR hN hs hw
    rw [hB.B12] at hVA ⊢
    rw [hB.B14 hA1, hW, hB.B7]
    exact lemma_2_22_iii hA1 (by norm_num) hVA.le _
  · rintro ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, hh, hs, hw, hφ, hB, hB13⟩
    obtain ⟨hA1, -, -, -, -, -, h6, hW3⟩ := hB.core hR hN hbN hs hw
    apply hB.dvd hR hN hbN hs hw
    have hW0 : 0 < W := by rw [hB.B11]; positivity
    exact pow_of_congruence (A := A) (B := 2 * R + 1) (C := C) (V := 2) (W := W)
      (by norm_num) hW0 (by omega) (by rw [show 3 * (2 * R + 1) = 6 * R + 3 by ring]; exact h6)
      hW3 (by rw [hB.B12] at hB13; exact hB13) (fun hA => by rw [hB.B14 hA, hB.B7])

/-- Lemma 2.25 with the `χ`-form congruence `D ≡ W + C(A − V) (mod 2AV − V² − 1)`,
`D² = (A²−1)C² + 1` in place of (B13) (remark after Lemma 2.28; used in Theorem 3 and §5). -/
theorem lemma_2_25' {R N b : ℕ} (hR : 8 ≤ R) (hN : 8 ≤ N) (hbR : b ≤ R) (hb : 0 < b)
    (hbN : b ≤ N) :
    (N ^ 2 ∣ (2 * R).choose R ∧ ∃ k, b = 2 ^ k) ↔
      ∃ h s w φ A B' C D K M P U V W Y : ℕ, 0 < h ∧ 0 < s ∧ 0 < w ∧ 0 < φ ∧
        B25core R N b h s w φ A B' C K M P U V W Y ∧
        D ≡ W + C * (A - V) [MOD 2 * A * V - V * V - 1] ∧
        D ^ 2 = (A ^ 2 - 1) * C ^ 2 + 1 := by
  constructor
  · rintro ⟨hdvd, hpow⟩
    obtain ⟨h, s, w, φ, A, B', C, K, M, P, U, V, W, Y, hh, hs, hw, hφ, hB, hW, -⟩ :=
      exists_B25core hR hN hbR hb hbN hdvd hpow
    obtain ⟨-, -, -, -, hA1, -, -, -, hVA, -⟩ := hB.sizes hR hN hs hw
    refine ⟨h, s, w, φ, A, B', C, χ hA1 (2 * R + 1), K, M, P, U, V, W, Y, hh, hs, hw, hφ, hB,
      ?_, ?_⟩
    · rw [hB.B12] at hVA ⊢
      rw [hB.B14 hA1, hW, hB.B7]
      exact χ_modEq_pow hA1 (by norm_num) hVA.le _
    · rw [hB.B14 hA1, hB.B7]
      have := χ_sq hA1 (2 * R + 1)
      have h2 : A ^ 2 - 1 = A * A - 1 := by rw [sq]
      rw [h2, sq, this]; ring
  · rintro ⟨h, s, w, φ, A, B', C, D, K, M, P, U, V, W, Y, hh, hs, hw, hφ, hB, hB13, hD⟩
    obtain ⟨hA1, -, -, -, -, -, h6, hW3⟩ := hB.core hR hN hbN hs hw
    apply hB.dvd hR hN hbN hs hw
    -- `D = χ_A(B')`
    obtain ⟨n, hDn, hCn⟩ := eq_pell_of_sq hA1 hD
    have hCψ : C = ψ hA1 (2 * R + 1) := by rw [hB.B14 hA1, hB.B7]
    have hn : n = 2 * R + 1 := (strictMono_y hA1).injective (by rw [← hCn, hCψ])
    rw [hn] at hDn
    rw [hB.B12] at hB13
    rw [hDn, hCψ] at hB13
    exact pow_of_χ_congruence (A := A) (B := 2 * R + 1) (V := 2) (by norm_num) (by omega)
      (by rw [show 3 * (2 * R + 1) = 6 * R + 3 by ring]; exact h6) hW3 hA1 hB13

end Jones1982
