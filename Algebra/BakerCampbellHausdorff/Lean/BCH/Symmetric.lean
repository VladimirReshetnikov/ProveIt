/-
# The symmetric (Strang) splitting and its second-order error (Proposition 11.3)

Proposition 11.3 of the accompanying article (`docs/combined`) concerns the
symmetric product `S₂(t) = e^{tX/2} e^{tY} e^{tX/2}`: its logarithm has no
degree-two term, so `S₂(t/n)^n = e^{t(X+Y)} + O(n^{-2})`, one order better than
the Trotter product.

This file proves the analytic content of that statement in a Banach algebra, by
two applications of the two-factor BCH theorem instead of the multifactor
formal expansion: with `A = tX/(2n)`, `B = tY/n`, `W = Z(A, B)` and
`L = Z(W, A)` one has `e^L = e^A e^B e^A`, and the degree-two contributions
`Z₂(A, B) + ½[A + B, A]` cancel, so `L = 2A + B + E` with `‖E‖ ≤ c₂ (‖A‖ + ‖B‖)³`
for an explicit constant `c₂` (`symmetric_log_bound`). Consequently

* `symmetric_expansion`: `S₂(t/n)^n = exp(t(X + Y) + Eₙ)` with `‖Eₙ‖ ≤ c₂ |t|³ a³ / n²`,
  `a = ‖X‖ + ‖Y‖`, for `n > 6 |t| a / log 2`;
* `symmetric_error`: `‖S₂(t/n)^n - e^{t(X+Y)}‖ ≤ e^{|t| a + c₂ |t|³ a³ / n²} · c₂ |t|³ a³ / n²`
  when `‖1‖ = 1`;
* `symmetric_limit`: `S₂(t/n)^n → e^{t(X+Y)}`.

The scalar lemma `neg_log_two_sub_exp_le`, `-log(2 - e^σ) ≤ 2σ` for `0 ≤ σ ≤ 1/4`,
controls the size of the intermediate logarithm `W`.
-/
import BCH.Trotter

open NormedSpace Finset Filter Topology

namespace BCH

/-- The constant `c₂ = c₀ + 28 c₀'` of the symmetric splitting error. -/
noncomputable def symC : ℝ := trotterC₀ + 28 * trotterC₀'

lemma symC_nonneg : 0 ≤ symC := by
  have h1 := trotterC₀_nonneg
  have h2 : 0 ≤ trotterC₀' := by
    unfold trotterC₀'
    have := log_two_sub_sqrt_two_nonneg
    have := Real.log_pos one_lt_two
    positivity
  unfold symC
  linarith

section Scalar

/-- `-log(2 - e^σ) ≤ 2σ` for `0 ≤ σ ≤ 1/4`. -/
lemma neg_log_two_sub_exp_le {σ : ℝ} (h0 : 0 ≤ σ) (h1 : σ ≤ 1 / 4) :
    -Real.log (2 - Real.exp σ) ≤ 2 * σ := by
  have hb := Real.abs_exp_sub_one_sub_id_le (x := σ) (by rw [abs_of_nonneg h0]; linarith)
  have hu : Real.exp σ - 1 ≤ 5 / 4 * σ := by
    have := (abs_le.mp hb).2
    nlinarith
  have hu0 : 0 ≤ Real.exp σ - 1 := by linarith [Real.add_one_le_exp σ]
  have hpos : 0 < 2 - Real.exp σ := by linarith
  have hlog : -Real.log (2 - Real.exp σ) ≤ (2 - Real.exp σ)⁻¹ - 1 := by
    rw [← Real.log_inv]
    exact Real.log_le_sub_one_of_pos (inv_pos.2 hpos)
  refine hlog.trans ?_
  rw [inv_eq_one_div, div_sub_one hpos.ne', div_le_iff₀ hpos]
  have h2 : 11 / 16 ≤ 2 - Real.exp σ := by linarith
  nlinarith [mul_nonneg h0 (by linarith : (0 : ℝ) ≤ 2 - Real.exp σ - 11 / 16)]

lemma quarter_lt_log_two : (1 : ℝ) / 4 < Real.log 2 := by
  rw [Real.lt_log_iff_exp_lt two_pos]
  have hb := Real.abs_exp_sub_one_sub_id_le (x := 1 / 4) (by rw [abs_of_nonneg (by norm_num)]; norm_num)
  have := (abs_le.mp hb).2
  norm_num at this ⊢
  linarith

lemma log_two_lt_one : Real.log 2 < 1 := by
  have := Real.log_lt_sub_one_of_pos (x := 2) two_pos (by norm_num)
  linarith

end Scalar

section Main

variable {𝕂 𝔸 : Type*} [RCLike 𝕂] [NormedRing 𝔸] [NormedAlgebra 𝕂 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
/-- `‖Z(A, B)‖ ≤ 2 (‖A‖ + ‖B‖)` when `‖A‖ + ‖B‖ ≤ 1/4`. -/
lemma norm_tsum_bchHom_le_two_mul (A B : 𝔸) (hσ : ‖A‖ + ‖B‖ ≤ 1 / 4) :
    ‖∑' n, bchHom 𝕂 A B n‖ ≤ 2 * (‖A‖ + ‖B‖) := by
  have hlog : ‖A‖ + ‖B‖ < Real.log 2 := hσ.trans_lt quarter_lt_log_two
  have hsum := summable_norm_bchHom (𝕂 := 𝕂) hlog
  calc ‖∑' n, bchHom 𝕂 A B n‖ ≤ ∑' n, ‖bchHom 𝕂 A B n‖ := norm_tsum_le_tsum_norm hsum
    _ = ∑' n, (1 : ℝ) ^ n * ‖bchHom 𝕂 A B n‖ := by simp
    _ ≤ -Real.log (2 - Real.exp (1 * (‖A‖ + ‖B‖))) :=
        tsum_pow_mul_norm_bchHom_le A B one_pos (by rw [one_mul]; exact hlog)
    _ ≤ 2 * (‖A‖ + ‖B‖) := by
        rw [one_mul]
        exact neg_log_two_sub_exp_le (add_nonneg (norm_nonneg _) (norm_nonneg _)) hσ

/-- **Proposition 11.3, the logarithm of the symmetric product**: for
`σ = ‖A‖ + ‖B‖ < log 2 / 6` put `W = Z(A, B)` and `L = Z(W, A)` (so that `e^L = e^A e^B e^A`).
Then the degree-two terms cancel and `‖L - (2A + B)‖ ≤ c₂ σ³`. -/
theorem symmetric_log_bound (A B : 𝔸) (hσ : ‖A‖ + ‖B‖ < Real.log 2 / 6) :
    ‖∑' n, bchHom 𝕂 (∑' n, bchHom 𝕂 A B n) A n - ((2 : 𝕂) • A + B)‖ ≤
      symC * (‖A‖ + ‖B‖) ^ 3 := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hlog1 := log_two_lt_one
  set σ := ‖A‖ + ‖B‖ with hσdef
  have hσ0 : 0 ≤ σ := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hσ4 : σ ≤ 1 / 4 := by linarith
  have hσ2 : σ < Real.log 2 / 2 := by linarith
  have hσlog : σ < Real.log 2 := by linarith
  have hAσ : ‖A‖ ≤ σ := by rw [hσdef]; linarith [norm_nonneg B]
  set W := ∑' n, bchHom 𝕂 A B n with hW
  have hWle : ‖W‖ ≤ 2 * σ := norm_tsum_bchHom_le_two_mul A B hσ4
  have hWA : ‖W‖ + ‖A‖ < Real.log 2 / 2 := by linarith
  have hWAlog : ‖W‖ + ‖A‖ < Real.log 2 := by linarith
  have hWA3 : ‖W‖ + ‖A‖ ≤ 3 * σ := by linarith
  -- summability
  have hABn := summable_norm_bchHom (𝕂 := 𝕂) hσlog
  have hAB : Summable fun n => bchHom 𝕂 A B n := hABn.of_norm
  have hWAn := summable_norm_bchHom (𝕂 := 𝕂) hWAlog
  have hWAs : Summable fun n => bchHom 𝕂 W A n := hWAn.of_norm
  -- the tails
  set T := ∑' i, bchHom 𝕂 A B (i + 3) with hT
  set V := ∑' i, bchHom 𝕂 A B (i + 2) with hV
  set T' := ∑' i, bchHom 𝕂 W A (i + 3) with hT'
  have hWeq : W = A + B + V := by
    have h : ∑' n, bchHom 𝕂 A B n =
        ∑ i ∈ range 2, bchHom 𝕂 A B i + ∑' i, bchHom 𝕂 A B (i + 2) :=
      (hAB.sum_add_tsum_nat_add 2).symm
    rw [hW, h, ← hV]
    simp [Finset.sum_range_succ, bchHom_zero, bchHom_one]
  have hVeq : V = (2 : 𝕂)⁻¹ • (A * B - B * A) + T := by
    have h2 : Summable fun i => bchHom 𝕂 A B (i + 2) :=
      (summable_nat_add_iff 2 (f := fun n => bchHom 𝕂 A B n)).2 hAB
    have h : ∑' i, bchHom 𝕂 A B (i + 2) =
        ∑ i ∈ range 1, bchHom 𝕂 A B (i + 2) + ∑' i, bchHom 𝕂 A B (i + 1 + 2) :=
      (h2.sum_add_tsum_nat_add 1).symm
    rw [hV, h, ← hT]
    simp [bchHom_two]
  have hLeq : ∑' n, bchHom 𝕂 W A n =
      (2 : 𝕂) • A + B + (T + (2 : 𝕂)⁻¹ • (V * A - A * V) + T') := by
    have h : ∑' n, bchHom 𝕂 W A n =
        ∑ i ∈ range 3, bchHom 𝕂 W A i + ∑' i, bchHom 𝕂 W A (i + 3) :=
      (hWAs.sum_add_tsum_nat_add 3).symm
    rw [h, ← hT']
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, bchHom_zero, bchHom_one,
      bchHom_two, zero_add]
    rw [hWeq, hVeq]
    simp only [mul_add, add_mul, mul_sub, sub_mul, smul_add, smul_sub, mul_smul_comm,
      smul_mul_assoc, smul_smul]
    module
  -- norm bounds for the pieces
  have hTle : ‖T‖ ≤ trotterC₀' * σ ^ 3 := by
    have hs : Summable fun i => ‖bchHom 𝕂 A B (i + 3)‖ :=
      (summable_nat_add_iff 3 (f := fun n => ‖bchHom 𝕂 A B n‖)).2 hABn
    exact (norm_tsum_le_tsum_norm hs).trans (tsum_norm_bchHom_tail_three_le A B hσ2)
  have hVle : ‖V‖ ≤ trotterC₀ * σ ^ 2 := by
    have hs : Summable fun i => ‖bchHom 𝕂 A B (i + 2)‖ :=
      (summable_nat_add_iff 2 (f := fun n => ‖bchHom 𝕂 A B n‖)).2 hABn
    exact (norm_tsum_le_tsum_norm hs).trans (tsum_norm_bchHom_tail_two_le A B hσ2)
  have hT'le : ‖T'‖ ≤ trotterC₀' * (3 * σ) ^ 3 := by
    have hs : Summable fun i => ‖bchHom 𝕂 W A (i + 3)‖ :=
      (summable_nat_add_iff 3 (f := fun n => ‖bchHom 𝕂 W A n‖)).2 hWAn
    refine (norm_tsum_le_tsum_norm hs).trans ((tsum_norm_bchHom_tail_three_le W A hWA).trans ?_)
    have hc : 0 ≤ trotterC₀' := by
      unfold trotterC₀'
      have := log_two_sub_sqrt_two_nonneg
      positivity
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (add_nonneg (norm_nonneg _) (norm_nonneg _)) hWA3 3) hc
  have hcomm : ‖(2 : 𝕂)⁻¹ • (V * A - A * V)‖ ≤ trotterC₀ * σ ^ 3 := by
    rw [norm_smul, norm_inv, RCLike.norm_two]
    have h1 : ‖V * A - A * V‖ ≤ 2 * ‖V‖ * ‖A‖ := by
      calc ‖V * A - A * V‖ ≤ ‖V * A‖ + ‖A * V‖ := norm_sub_le _ _
        _ ≤ ‖V‖ * ‖A‖ + ‖A‖ * ‖V‖ := add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
        _ = 2 * ‖V‖ * ‖A‖ := by ring
    have hc0 := trotterC₀_nonneg
    calc (2 : ℝ)⁻¹ * ‖V * A - A * V‖ ≤ (2 : ℝ)⁻¹ * (2 * ‖V‖ * ‖A‖) :=
          mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = ‖V‖ * ‖A‖ := by ring
      _ ≤ (trotterC₀ * σ ^ 2) * σ :=
          mul_le_mul hVle hAσ (norm_nonneg _) (by positivity)
      _ = trotterC₀ * σ ^ 3 := by ring
  rw [hLeq, add_sub_cancel_left]
  calc ‖T + (2 : 𝕂)⁻¹ • (V * A - A * V) + T'‖
      ≤ ‖T‖ + ‖(2 : 𝕂)⁻¹ • (V * A - A * V)‖ + ‖T'‖ := norm_add₃_le
    _ ≤ trotterC₀' * σ ^ 3 + trotterC₀ * σ ^ 3 + trotterC₀' * (3 * σ) ^ 3 :=
        add_le_add (add_le_add hTle hcomm) hT'le
    _ = symC * σ ^ 3 := by unfold symC; ring

omit [CompleteSpace 𝔸] in
/-- The scaled elements of the symmetric product: `‖tX/(2n)‖ + ‖tY/n‖ ≤ |t| (‖X‖ + ‖Y‖) / n`. -/
lemma symmetric_scale_norm (X Y : 𝔸) (t : 𝕂) {n : ℕ} (hn : 0 < n) :
    ‖(t / (2 * n)) • X‖ + ‖(t / n) • Y‖ ≤ ‖t‖ * (‖X‖ + ‖Y‖) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [norm_smul, norm_smul, norm_div, norm_div, RCLike.norm_natCast, norm_mul, RCLike.norm_two,
    RCLike.norm_natCast]
  have h1 : ‖t‖ / (2 * n) * ‖X‖ ≤ ‖t‖ / n * ‖X‖ :=
    mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_left (norm_nonneg _) hnR (by linarith))
      (norm_nonneg _)
  calc ‖t‖ / (2 * n) * ‖X‖ + ‖t‖ / n * ‖Y‖ ≤ ‖t‖ / n * ‖X‖ + ‖t‖ / n * ‖Y‖ :=
        add_le_add h1 le_rfl
    _ = ‖t‖ * (‖X‖ + ‖Y‖) / n := by ring

/-- **Proposition 11.3, the exponent of `S₂(t/n)^n`**: for `n > 6 |t| a / log 2`,
`a = ‖X‖ + ‖Y‖`, `S₂(t/n)^n = exp(t(X + Y) + Eₙ)` with `‖Eₙ‖ ≤ c₂ |t|³ a³ / n²`. -/
theorem symmetric_expansion (X Y : 𝔸) (t : 𝕂) {n : ℕ}
    (hn : 6 * ‖t‖ * (‖X‖ + ‖Y‖) < n * Real.log 2) :
    ∃ E : 𝔸, ‖E‖ ≤ symC * (‖t‖ * (‖X‖ + ‖Y‖)) ^ 3 / (n : ℝ) ^ 2 ∧
      (exp ((t / (2 * n)) • X) * exp ((t / n) • Y) * exp ((t / (2 * n)) • X)) ^ n =
        exp (t • (X + Y) + E) := by
  let +nondep : NormedAlgebra ℚ 𝔸 := .restrictScalars ℚ 𝕂 𝔸
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hn0 : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h
      have : (0 : ℝ) ≤ 6 * ‖t‖ * (‖X‖ + ‖Y‖) := by positivity
      simp at hn
      linarith
    · exact h
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  set A := (t / (2 * n)) • X with hA
  set B := (t / n) • Y with hB
  have hσ : ‖A‖ + ‖B‖ < Real.log 2 / 6 := by
    refine (symmetric_scale_norm X Y t hn0).trans_lt ?_
    rw [div_lt_div_iff₀ hnR (by norm_num : (0 : ℝ) < 6)]
    linarith
  have hσlog : ‖A‖ + ‖B‖ < Real.log 2 := by linarith
  set W := ∑' k, bchHom 𝕂 A B k with hW
  have hWA : ‖W‖ + ‖A‖ < Real.log 2 := by
    have := norm_tsum_bchHom_le_two_mul (𝕂 := 𝕂) A B (by linarith [log_two_lt_one])
    have hAσ : ‖A‖ ≤ ‖A‖ + ‖B‖ := by linarith [norm_nonneg B]
    linarith
  set L := ∑' k, bchHom 𝕂 W A k with hL
  have heL : exp L = exp A * exp B * exp A := by
    rw [hL, exp_tsum_bchHom hWA, hW, exp_tsum_bchHom hσlog]
  have hbound := symmetric_log_bound (𝕂 := 𝕂) A B hσ
  rw [← hW, ← hL] at hbound
  refine ⟨(n : ℕ) • (L - ((2 : 𝕂) • A + B)), ?_, ?_⟩
  · rw [← Nat.cast_smul_eq_nsmul 𝕂, norm_smul, RCLike.norm_natCast]
    calc (n : ℝ) * ‖L - ((2 : 𝕂) • A + B)‖
        ≤ (n : ℝ) * (symC * (‖A‖ + ‖B‖) ^ 3) := mul_le_mul_of_nonneg_left hbound hnR.le
      _ ≤ (n : ℝ) * (symC * (‖t‖ * (‖X‖ + ‖Y‖) / n) ^ 3) := by
          gcongr
          · exact symC_nonneg
          · exact symmetric_scale_norm X Y t hn0
      _ = symC * (‖t‖ * (‖X‖ + ‖Y‖)) ^ 3 / (n : ℝ) ^ 2 := by
          field_simp
  · rw [← heL, ← exp_nsmul]
    congr 1
    have h2AB : (2 : 𝕂) • A + B = (t / n) • (X + Y) := by
      rw [hA, hB, smul_smul, smul_add]
      congr 2
      field_simp
    rw [← Nat.cast_smul_eq_nsmul 𝕂, ← Nat.cast_smul_eq_nsmul 𝕂, smul_sub, h2AB, smul_smul,
      mul_div_cancel₀ t (Nat.cast_ne_zero.mpr hn0.ne'), add_sub_cancel]

/-- **Proposition 11.3, the second-order error**: in a Banach algebra with `‖1‖ = 1`, for
`n > 6 |t| a / log 2`, `a = ‖X‖ + ‖Y‖`,
`‖S₂(t/n)^n - e^{t(X+Y)}‖ ≤ e^{|t| a + c₂ |t|³ a³ / n²} · c₂ |t|³ a³ / n²`. -/
theorem symmetric_error [NormOneClass 𝔸] (X Y : 𝔸) (t : 𝕂) {n : ℕ}
    (hn : 6 * ‖t‖ * (‖X‖ + ‖Y‖) < n * Real.log 2) :
    ‖(exp ((t / (2 * n)) • X) * exp ((t / n) • Y) * exp ((t / (2 * n)) • X)) ^ n -
        exp (t • (X + Y))‖ ≤
      Real.exp (‖t‖ * (‖X‖ + ‖Y‖) + symC * (‖t‖ * (‖X‖ + ‖Y‖)) ^ 3 / (n : ℝ) ^ 2) *
        (symC * (‖t‖ * (‖X‖ + ‖Y‖)) ^ 3 / (n : ℝ) ^ 2) := by
  obtain ⟨E, hE, hexp⟩ := symmetric_expansion X Y t hn
  rw [hexp]
  have hbound := norm_exp_sub_exp_le 𝕂 (t • (X + Y)) (t • (X + Y) + E)
  rw [norm_one, one_pow, one_mul, add_sub_cancel_left] at hbound
  refine hbound.trans ?_
  have hS : ‖t • (X + Y)‖ ≤ ‖t‖ * (‖X‖ + ‖Y‖) := by
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left (norm_add_le _ _) (norm_nonneg _)
  have hmax : max ‖t • (X + Y)‖ ‖t • (X + Y) + E‖ ≤ ‖t‖ * (‖X‖ + ‖Y‖) + ‖E‖ :=
    max_le (by linarith [norm_nonneg E]) ((norm_add_le _ _).trans (by linarith))
  exact mul_le_mul (Real.exp_le_exp.mpr (hmax.trans (by linarith))) hE (norm_nonneg _)
    (Real.exp_pos _).le

/-- **Proposition 11.3, the limit**: `S₂(t/n)^n → e^{t(X+Y)}` in a Banach algebra with
`‖1‖ = 1`. -/
theorem symmetric_limit [NormOneClass 𝔸] (X Y : 𝔸) (t : 𝕂) :
    Tendsto (fun n : ℕ =>
      (exp ((t / (2 * n)) • X) * exp ((t / n) • Y) * exp ((t / (2 * n)) • X)) ^ n) atTop
      (𝓝 (exp (t • (X + Y)))) := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos one_lt_two
  set q := symC * (‖t‖ * (‖X‖ + ‖Y‖)) ^ 3 with hq
  have hq0 : 0 ≤ q := by
    have := symC_nonneg
    positivity
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun n => norm_nonneg _) ?_
    (tendsto_const_div_atTop_nhds_zero_nat (Real.exp (‖t‖ * (‖X‖ + ‖Y‖) + q) * q))
  filter_upwards [eventually_gt_atTop ⌈6 * ‖t‖ * (‖X‖ + ‖Y‖) / Real.log 2⌉₊,
    eventually_ge_atTop 1] with n hn hn1
  have hn' : 6 * ‖t‖ * (‖X‖ + ‖Y‖) < n * Real.log 2 := by
    have h1 : 6 * ‖t‖ * (‖X‖ + ‖Y‖) / Real.log 2 < n :=
      (Nat.le_ceil _).trans_lt (by exact_mod_cast hn)
    rw [div_lt_iff₀ hlog2] at h1
    linarith
  have hn1R : (1 : ℝ) ≤ n := by exact_mod_cast hn1
  have hn2 : (n : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
  have hqn : q / (n : ℝ) ^ 2 ≤ q / n := div_le_div_of_nonneg_left hq0 (by linarith) hn2
  refine (symmetric_error X Y t hn').trans ?_
  calc Real.exp (‖t‖ * (‖X‖ + ‖Y‖) + q / (n : ℝ) ^ 2) * (q / (n : ℝ) ^ 2)
      ≤ Real.exp (‖t‖ * (‖X‖ + ‖Y‖) + q) * (q / n) := by
        refine mul_le_mul (Real.exp_le_exp.mpr ?_) hqn (by positivity) (Real.exp_pos _).le
        have : q / (n : ℝ) ^ 2 ≤ q := div_le_self hq0 (by nlinarith)
        linarith
    _ = _ := (mul_div_assoc _ _ _).symm

end Main

end BCH
