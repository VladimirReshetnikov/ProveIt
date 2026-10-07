import OAI.Combinatorics.Progressions.Results.Basic

namespace OAI

section

namespace Erdos3.BohrWidthBudget

theorem selector_scale_lower_bound {d D : ℝ} (hd : 0 < d) (hD : 0 ≤ D) :
    1 / (1000 * d * (D + 1)) ≤
      (100 * (2 * d) * ((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ))⁻¹ := by
  have hceil := (Nat.ceil_lt_add_one hD).le
  have hsmall : (((2 * (⌈D⌉₊ + 1) + 1 : ℕ) : ℝ)) ≤ 5 * (D + 1) := by
    push_cast
    linarith
  rw [← one_div]
  apply one_div_le_one_div_of_le (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hsmall (show 0 ≤ 100 * (2 * d) by positivity)
  nlinarith

theorem polynomial_denominator_le_exp {W p d : ℝ}
    (hW : 0 < W) (hp : 0 ≤ p) (hd : 1 ≤ d) :
    Real.exp p * W * d ^ 3 * (p + 1) ^ 4 ≤
      Real.exp ((W + 8) * (1 + p + Real.log (2 + d))) := by
  have hWexp : W ≤ Real.exp W := by linarith [Real.add_one_le_exp W]
  have hd0 : 0 ≤ d := by linarith
  have hdlog : d ^ 3 ≤ Real.exp (3 * Real.log (2 + d)) := by
    calc
      d ^ 3 ≤ (2 + d) ^ 3 := pow_le_pow_left₀ hd0 (by linarith) 3
      _ = Real.exp (3 * Real.log (2 + d)) := by
        simpa only [Nat.cast_ofNat, Real.exp_log (by positivity : 0 < 2 + d)] using
          (Real.exp_nat_mul (Real.log (2 + d)) 3).symm
  have hppow : (p + 1) ^ 4 ≤ Real.exp (4 * p) := by
    calc
      (p + 1) ^ 4 ≤ Real.exp p ^ 4 :=
        pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp p) 4
      _ = Real.exp (4 * p) := by
        simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul p 4).symm
  have hlog : 0 ≤ Real.log (2 + d) := Real.log_nonneg (by linarith)
  calc
    Real.exp p * W * d ^ 3 * (p + 1) ^ 4 ≤
        Real.exp p * Real.exp W * Real.exp (3 * Real.log (2 + d)) * Real.exp (4 * p) := by
      gcongr
    _ = Real.exp (p + W + 3 * Real.log (2 + d) + 4 * p) := by
      rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
    _ ≤ Real.exp ((W + 8) * (1 + p + Real.log (2 + d))) := by
      apply Real.exp_le_exp.mpr
      nlinarith [mul_nonneg hW.le hp, mul_nonneg hW.le hlog]

theorem exp_neg_budget_le_reciprocal {W p d : ℝ}
    (hW : 0 < W) (hp : 0 ≤ p) (hd : 1 ≤ d) :
    Real.exp (-((W + 8) * (1 + p + Real.log (2 + d)))) ≤
      1 / (Real.exp p * W * d ^ 3 * (p + 1) ^ 4) := by
  rw [Real.exp_neg, ← one_div]
  exact one_div_le_one_div_of_le (by positivity)
    (polynomial_denominator_le_exp hW hp hd)

end Erdos3.BohrWidthBudget

end

section

namespace Erdos3.BohrWidthBudget

theorem rational_width_lower_bound {u d D w v a : ℝ}
    (hu : 0 < u) (hd : 1 ≤ d) (hD : 0 ≤ D) (hw : 0 < w) (hw1 : w ≤ 1)
    (hv : w / (400 * d) ≤ v) (ha : 1 / (1000 * d * (D + 1)) ≤ a) :
    u * w / (10240000000 * d ^ 3 * (D + 1)) ≤
      min ((u / (6400 * d)) * (a * v / 2)) (u / (8 * (D + 1))) / 2 := by
  have hd0 : 0 < d := by linarith
  have ha0 : 0 < a := lt_of_lt_of_le (by positivity) ha
  have hprod : (1 / (1000 * d * (D + 1))) * (w / (400 * d)) ≤ a * v :=
    mul_le_mul ha hv (by positivity) ha0.le
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply le_min
  · calc
      u * w / (10240000000 * d ^ 3 * (D + 1)) * 2 =
          (u / (6400 * d)) * ((1 / (1000 * d * (D + 1))) * (w / (400 * d)) / 2) := by
        field_simp
        ring
      _ ≤ (u / (6400 * d)) * (a * v / 2) :=
        mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod (by norm_num)) (by positivity)
  · have hd3 : 1 ≤ d ^ 3 := one_le_pow₀ hd
    have hfrac : w / (5120000000 * d ^ 3) ≤ 1 / 8 := by
      rw [div_le_iff₀ (by positivity)]
      nlinarith
    calc
      u * w / (10240000000 * d ^ 3 * (D + 1)) * 2 =
          (u / (D + 1)) * (w / (5120000000 * d ^ 3)) := by
        field_simp
        ring
      _ ≤ (u / (D + 1)) * (1 / 8) := mul_le_mul_of_nonneg_left hfrac (by positivity)
      _ = u / (8 * (D + 1)) := by field_simp

theorem rational_width_ge_exponential {epsilon C p d w : ℝ}
    (hepsilon : 0 < epsilon) (hC : 0 ≤ C) (hp : 0 ≤ p) (hd : 1 ≤ d) (hw : 0 ≤ w) :
    let W := 10240000000 * (C + 1) / epsilon
    w * Real.exp (-((W + 8) * (1 + p + Real.log (2 + d)))) ≤
      epsilon * Real.exp (-p) * w / (10240000000 * d ^ 3 * (C * (p + 1) ^ 4 + 1)) := by
  intro W
  have hW : 0 < W := by dsimp [W]; positivity
  have hd0 : 0 < d := by linarith
  have hbound := mul_le_mul_of_nonneg_left (exp_neg_budget_le_reciprocal hW hp hd) hw
  have hp4 : 1 ≤ (p + 1) ^ 4 := one_le_pow₀ (show 1 ≤ p + 1 by linarith)
  have hden : 10240000000 * d ^ 3 * (C * (p + 1) ^ 4 + 1) ≤
      10240000000 * d ^ 3 * ((C + 1) * (p + 1) ^ 4) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    nlinarith
  calc
    w * Real.exp (-((W + 8) * (1 + p + Real.log (2 + d)))) ≤
        w * (1 / (Real.exp p * W * d ^ 3 * (p + 1) ^ 4)) := hbound
    _ = epsilon * Real.exp (-p) * w /
        (10240000000 * d ^ 3 * ((C + 1) * (p + 1) ^ 4)) := by
      rw [Real.exp_neg]
      dsimp [W]
      field_simp
    _ ≤ epsilon * Real.exp (-p) * w /
        (10240000000 * d ^ 3 * (C * (p + 1) ^ 4 + 1)) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden

end Erdos3.BohrWidthBudget

end

end OAI
