import GowersSzemeredi.Proofs16VarietyControlAbsorption

/-! The logarithmic loss of the variety route is linear in a master bound.

The absorption step needs `L ≥ log W⁻¹` and `L ≥ log(81·7⁴Q² + 27)`. Here `W`
is the `ρ`-free factor of the ceiling-free width exponent
(`section16VarietyCeilingFreeWidthCoeff`, with the joint exponent
`E = 1/(1024·ps²·(4Cs+18)·(n+1)^17·(mb'+2)^17)` substituted). `W⁻¹` is a
product of 112 factors, counted with multiplicity. `variety_loss_le` shows
that if every factor is at most `e^Λ`, with `Λ ≥ 7`, both logarithms are at
most `112·Λ`. The factors are the counts, the Milićević bounds, the named
constants and the logarithmic term; `1024 ≤ e^7` covers the numerals. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- `1024 ≤ e^7`. -/
theorem thousand_twenty_four_le_exp_seven : (1024 : Real) ≤ Real.exp 7 := by
  have he := Real.exp_one_gt_d9
  have h7 : Real.exp 7 = Real.exp 1 ^ 7 := by rw [← Real.exp_nat_mul]; norm_num
  rw [h7]
  calc (1024 : Real) ≤ 2.7182818283 ^ 7 := by norm_num
    _ ≤ Real.exp 1 ^ 7 := pow_le_pow_left₀ (by norm_num) he.le 7

/-- **The logarithmic losses are at most `112·Λ`.** -/
theorem variety_loss_le {p q pv Cv mb Q Lg ps Cs n mb' Λ : Real} (hΛ : 7 ≤ Λ)
    (hp : 1 ≤ p) (hpΛ : p ≤ Real.exp Λ) (hq : 0 ≤ q) (hqΛ : q + 1 ≤ Real.exp Λ)
    (hpv : 1 ≤ pv) (hpvΛ : pv ≤ Real.exp Λ) (hCv : 0 ≤ Cv) (hCvΛ : 4 * Cv + 18 ≤ Real.exp Λ)
    (hmb : 0 ≤ mb) (hmbΛ : mb + 2 ≤ Real.exp Λ) (hQ : 0 ≤ Q) (hQΛ : Q + 1 ≤ Real.exp Λ)
    (hLg : 1 ≤ Lg) (hLgΛ : Lg ≤ Real.exp Λ) (hps : 1 ≤ ps) (hpsΛ : ps ≤ Real.exp Λ)
    (hCs : 0 ≤ Cs) (hCsΛ : 4 * Cs + 18 ≤ Real.exp Λ) (hn : 0 ≤ n) (hnΛ : n + 1 ≤ Real.exp Λ)
    (hmb' : 0 ≤ mb') (hmb'Λ : mb' + 2 ≤ Real.exp Λ) :
    let E := 1 / (1024 * ps ^ 2 * (4 * Cs + 18) * (n + 1) ^ 17 * (mb' + 2) ^ 17)
    let W := E / (8 * p * (q + 1) ^ 16) /
      (1024 * pv ^ 2 * (4 * Cv + 18) * (mb + 2) ^ 17 * (7 ^ 17 * (Q + 1) ^ 17)) / Lg
    0 < W ∧ Real.log W⁻¹ ≤ 112 * Λ ∧ Real.log (81 * 7 ^ 4 * Q ^ 2 + 27) ≤ 112 * Λ := by
  intro E W
  obtain ⟨e, he⟩ : ∃ e, Real.exp Λ = e := ⟨_, rfl⟩
  rw [he] at hpΛ hqΛ hpvΛ hCvΛ hmbΛ hQΛ hLgΛ hpsΛ hCsΛ hnΛ hmb'Λ
  have h1024 : (1024 : Real) ≤ e := by
    rw [← he]; exact thousand_twenty_four_le_exp_seven.trans (Real.exp_le_exp.mpr hΛ)
  have he0 : 0 < e := by linarith
  have h7 : (7 : Real) ≤ e := by linarith
  have h8 : (8 : Real) ≤ e := by linarith
  -- the three products, bounded one at a time
  have hA : 8 * p * (q + 1) ^ 16 ≤ e ^ 18 := by
    calc 8 * p * (q + 1) ^ 16 ≤ e * e * e ^ 16 := by
          apply mul_le_mul (mul_le_mul h8 hpΛ (by linarith) he0.le)
            (pow_le_pow_left₀ (by linarith) hqΛ 16) (by positivity) (by positivity)
      _ = e ^ 18 := by ring
  have hB : 1024 * pv ^ 2 * (4 * Cv + 18) * (mb + 2) ^ 17 * (7 ^ 17 * (Q + 1) ^ 17) ≤ e ^ 55 := by
    have b1 : 1024 * pv ^ 2 ≤ e * e ^ 2 :=
      mul_le_mul h1024 (pow_le_pow_left₀ (by linarith) hpvΛ 2) (by positivity) he0.le
    have b2 : 1024 * pv ^ 2 * (4 * Cv + 18) ≤ e * e ^ 2 * e :=
      mul_le_mul b1 hCvΛ (by linarith) (by positivity)
    have b3 : 1024 * pv ^ 2 * (4 * Cv + 18) * (mb + 2) ^ 17 ≤ e * e ^ 2 * e * e ^ 17 :=
      mul_le_mul b2 (pow_le_pow_left₀ (by linarith) hmbΛ 17) (by positivity) (by positivity)
    have b4 : (7 : Real) ^ 17 * (Q + 1) ^ 17 ≤ e ^ 17 * e ^ 17 :=
      mul_le_mul (pow_le_pow_left₀ (by norm_num) h7 17) (pow_le_pow_left₀ (by linarith) hQΛ 17)
        (by positivity) (by positivity)
    calc 1024 * pv ^ 2 * (4 * Cv + 18) * (mb + 2) ^ 17 * (7 ^ 17 * (Q + 1) ^ 17)
        ≤ e * e ^ 2 * e * e ^ 17 * (e ^ 17 * e ^ 17) :=
          mul_le_mul b3 b4 (by positivity) (by positivity)
      _ = e ^ 55 := by ring
  have hF : 1024 * ps ^ 2 * (4 * Cs + 18) * (n + 1) ^ 17 * (mb' + 2) ^ 17 ≤ e ^ 38 := by
    have f1 : 1024 * ps ^ 2 ≤ e * e ^ 2 :=
      mul_le_mul h1024 (pow_le_pow_left₀ (by linarith) hpsΛ 2) (by positivity) he0.le
    have f2 : 1024 * ps ^ 2 * (4 * Cs + 18) ≤ e * e ^ 2 * e :=
      mul_le_mul f1 hCsΛ (by linarith) (by positivity)
    have f3 : 1024 * ps ^ 2 * (4 * Cs + 18) * (n + 1) ^ 17 ≤ e * e ^ 2 * e * e ^ 17 :=
      mul_le_mul f2 (pow_le_pow_left₀ (by linarith) hnΛ 17) (by positivity) (by positivity)
    calc 1024 * ps ^ 2 * (4 * Cs + 18) * (n + 1) ^ 17 * (mb' + 2) ^ 17
        ≤ e * e ^ 2 * e * e ^ 17 * e ^ 17 :=
          mul_le_mul f3 (pow_le_pow_left₀ (by linarith) hmb'Λ 17) (by positivity) (by positivity)
      _ = e ^ 38 := by ring
  -- `W⁻¹ = A·B·Lg·F` on atoms
  have hA0 : 0 < 8 * p * (q + 1) ^ 16 := by
    have : 0 < q + 1 := by linarith
    positivity
  have hB0 : 0 < 1024 * pv ^ 2 * (4 * Cv + 18) * (mb + 2) ^ 17 * (7 ^ 17 * (Q + 1) ^ 17) := by
    have : 0 < mb + 2 := by linarith
    have : 0 < Q + 1 := by linarith
    have : 0 < 4 * Cv + 18 := by linarith
    positivity
  have hF0 : 0 < 1024 * ps ^ 2 * (4 * Cs + 18) * (n + 1) ^ 17 * (mb' + 2) ^ 17 := by
    have : 0 < mb' + 2 := by linarith
    have : 0 < n + 1 := by linarith
    have : 0 < 4 * Cs + 18 := by linarith
    positivity
  have hLg0 : 0 < Lg := by linarith
  simp only [W, E]
  generalize 8 * p * (q + 1) ^ 16 = A at hA hA0 ⊢
  generalize 1024 * pv ^ 2 * (4 * Cv + 18) * (mb + 2) ^ 17 * (7 ^ 17 * (Q + 1) ^ 17) = B at hB hB0 ⊢
  generalize 1024 * ps ^ 2 * (4 * Cs + 18) * (n + 1) ^ 17 * (mb' + 2) ^ 17 = F at hF hF0 ⊢
  have hWinv : (1 / F / A / B / Lg)⁻¹ = A * B * Lg * F := by
    field_simp
  have hWpos : 0 < (1 / F / A / B / Lg)⁻¹ := by rw [hWinv]; positivity
  have hWle : (1 / F / A / B / Lg)⁻¹ ≤ e ^ 112 := by
    rw [hWinv]
    calc A * B * Lg * F ≤ e ^ 18 * e ^ 55 * e * e ^ 38 :=
          mul_le_mul (mul_le_mul (mul_le_mul hA hB hB0.le (by positivity)) hLgΛ hLg0.le
            (by positivity)) hF hF0.le (by positivity)
      _ = e ^ 112 := by ring
  have hlogW : Real.log (1 / F / A / B / Lg)⁻¹ ≤ 112 * Λ := by
    calc Real.log (1 / F / A / B / Lg)⁻¹ ≤ Real.log (e ^ 112) := Real.log_le_log hWpos hWle
      _ = 112 * Λ := by rw [Real.log_pow, ← he, Real.log_exp]; norm_num
  refine ⟨inv_pos.mp hWpos, hlogW, ?_⟩
  have hQe : 81 * 7 ^ 4 * Q ^ 2 + 27 ≤ e ^ 7 := by
    calc 81 * 7 ^ 4 * Q ^ 2 + 27 ≤ e * e ^ 4 * (Q + 1) ^ 2 := by
          have h1 : (108 * 7 ^ 4 : Real) ≤ e * e ^ 4 :=
            mul_le_mul (by linarith) (pow_le_pow_left₀ (by norm_num) h7 4) (by norm_num) he0.le
          have h2 : 81 * 7 ^ 4 * Q ^ 2 + 27 ≤ 108 * 7 ^ 4 * (Q + 1) ^ 2 := by nlinarith [sq_nonneg Q]
          exact h2.trans (mul_le_mul_of_nonneg_right h1 (by positivity))
      _ ≤ e * e ^ 4 * e ^ 2 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) hQΛ 2) (by positivity)
      _ = e ^ 7 := by ring
  calc Real.log (81 * 7 ^ 4 * Q ^ 2 + 27) ≤ Real.log (e ^ 7) := Real.log_le_log (by positivity) hQe
    _ = 7 * Λ := by rw [Real.log_pow, ← he, Real.log_exp]; norm_num
    _ ≤ 112 * Λ := by linarith

end LeanProofs.GowersSzemeredi
