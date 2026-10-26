import Diophantine.Paper1980.PellRatio90

namespace NewSimplifications
open Diophantine Pell

theorem upper_estimate_budget {U Y r k c a J : ℕ} {scale : ℝ} (hscale : 0 < scale) (hU : 1 ≤ U) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hJ : J = 2 * r + 1) (hA : 1 < a + 2) (ha : a = Y * (U + 1))
    (hP : 1 < 2 * (U * Y ^ 2) + 1) (hc : c = ψ hA J) (hk : k = ψ hP (r + 1))
    (hξY' : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < scale * (Y + 1))
    (h72 : 72 * r < U + 1) (h16 : 16 ≤ Y * (U + 1)) :
    (c : ℝ) / k < ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r + scale / 2 := by
  have hk0 : 0 < k := by
    rw [hk]; exact lt_of_lt_of_le (Nat.succ_pos r) (Pell.yn_ge_n hP (r + 1))
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
  have hUR : (0 : ℝ) < (U : ℝ) ^ r := by positivity
  have hU1 : (0 : ℝ) < (U : ℝ) + 1 := by positivity
  have hYR : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have hYU : (0 : ℝ) < (Y : ℝ) * (U + 1) := by positivity
  have haR : (a : ℝ) = Y * (U + 1) := by rw [ha]; push_cast; ring
  set ξ : ℝ := ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r with hξ
  have hξdef : ((U : ℝ) + 1) ^ (2 * r) = ξ * (U : ℝ) ^ r := by rw [hξ]; field_simp
  -- growth bounds
  have hcb : (c : ℝ) ≤ (2 * ((a : ℝ) + 2)) ^ (2 * r) := by
    have := ψ_succ_le_pow hA (2 * r)
    rw [← hJ, ← hc] at this
    exact_mod_cast this
  have hkb : ((2 * (2 * (U * Y ^ 2) + 1) - 1 : ℕ) : ℝ) ^ r ≤ k := by
    have := pow_le_ψ_succ hP r
    rw [← hk] at this
    exact_mod_cast this
  -- `Z = (2A)² U ≤ X (1 + ε)`, `X = (2P−1)(U+1)²`, `ε = 9/(Y(U+1))`
  set X : ℝ := ((2 * (2 * (U * Y ^ 2) + 1) - 1 : ℕ) : ℝ) * ((U : ℝ) + 1) ^ 2 with hX
  set Z : ℝ := (2 * ((a : ℝ) + 2)) ^ 2 * U with hZ
  set ε : ℝ := 9 / ((Y : ℝ) * (U + 1)) with hε
  have hε0 : 0 ≤ ε := by rw [hε]; positivity
  have hXpos : 0 < X := by
    rw [hX]
    have : (1 : ℕ) ≤ 2 * (2 * (U * Y ^ 2) + 1) - 1 := by omega
    have : (1 : ℝ) ≤ ((2 * (2 * (U * Y ^ 2) + 1) - 1 : ℕ) : ℝ) := by exact_mod_cast this
    positivity
  have hZX : Z ≤ X * (1 + ε) := by
    have key := Jones1980.Ratio90.upper_key hU hY h16
    have keyR : Z * ((Y : ℝ) * (U + 1)) ≤ X * ((Y : ℝ) * (U + 1) + 9) := by
      rw [hZ, hX, haR]
      exact_mod_cast key
    have e : X * (1 + ε) = X * ((Y : ℝ) * (U + 1) + 9) / ((Y : ℝ) * (U + 1)) := by
      rw [hε]; field_simp
    rw [e, le_div_iff₀ hYU]
    exact keyR
  -- `c U^r ≤ Z^r` and `X^r ≤ k (U+1)^(2r)`
  have hcZ : (c : ℝ) * (U : ℝ) ^ r ≤ Z ^ r := by
    have e : Z ^ r = (2 * ((a : ℝ) + 2)) ^ (2 * r) * (U : ℝ) ^ r := by
      rw [hZ, mul_pow, ← pow_mul]
    rw [e]; exact mul_le_mul_of_nonneg_right hcb hUR.le
  have hXk : X ^ r ≤ (k : ℝ) * ((U : ℝ) + 1) ^ (2 * r) := by
    have e : X ^ r = ((2 * (2 * (U * Y ^ 2) + 1) - 1 : ℕ) : ℝ) ^ r * ((U : ℝ) + 1) ^ (2 * r) := by
      rw [hX, mul_pow, ← pow_mul]
    rw [e]; exact mul_le_mul_of_nonneg_right hkb (by positivity)
  -- `(1+ε)^r ≤ 1 + 2rε`
  have h72R : (72 : ℝ) * r < U + 1 := by exact_mod_cast h72
  have hrε : (r : ℝ) * ε ≤ 1 / 2 := by
    rw [hε, mul_div_assoc', div_le_iff₀ hYU]
    nlinarith
  have hpow := Jones1980.Ratio90.one_add_pow_le r hε0 hrε
  -- `c U^r ≤ k ξ U^r (1 + 2rε)`, hence `c ≤ k ξ (1 + 2rε)`
  have h1 : (c : ℝ) * (U : ℝ) ^ r ≤ (k : ℝ) * ξ * (1 + 2 * (r * ε)) * (U : ℝ) ^ r := by
    calc (c : ℝ) * (U : ℝ) ^ r ≤ Z ^ r := hcZ
      _ ≤ (X * (1 + ε)) ^ r := pow_le_pow_left₀ (by rw [hZ]; positivity) hZX r
      _ = X ^ r * (1 + ε) ^ r := mul_pow _ _ _
      _ ≤ (k : ℝ) * ((U : ℝ) + 1) ^ (2 * r) * (1 + 2 * (r * ε)) := by
          apply mul_le_mul hXk hpow (by positivity) (by positivity)
      _ = (k : ℝ) * ξ * (1 + 2 * (r * ε)) * (U : ℝ) ^ r := by rw [hξdef]; ring
  have h1' : (c : ℝ) ≤ (k : ℝ) * ξ * (1 + 2 * (r * ε)) := le_of_mul_le_mul_right h1 hUR
  have hξY : ξ < scale * (Y + 1) := by rw [hξ]; exact hξY'
  -- The supplied ratio budget scales the final error.
  have hsmall : ξ * (2 * (r * ε)) < scale / 2 := by
    have hε' : (Y + 1 : ℝ) * (2 * (r * ε)) < 1 / 2 := by
      rw [hε]
      have e : ((Y : ℝ) + 1) * (2 * (r * (9 / ((Y : ℝ) * (U + 1))))) =
          18 * r * (Y + 1) / (Y * (U + 1)) := by field_simp; ring
      rw [e, div_lt_iff₀ hYU]
      nlinarith
    have hξ0 : 0 ≤ ξ := by rw [hξ]; positivity
    calc ξ * (2 * (r * ε)) ≤ scale * (Y + 1 : ℝ) * (2 * (r * ε)) :=
          mul_le_mul_of_nonneg_right hξY.le (by positivity)
      _ = scale * ((Y + 1 : ℝ) * (2 * (r * ε))) := by ring
      _ < scale * (1 / 2) := mul_lt_mul_of_pos_left hε' hscale
      _ = scale / 2 := by ring
  -- conclude
  rw [div_lt_iff₀ hkR]
  calc (c : ℝ) ≤ k * ξ * (1 + 2 * (r * ε)) := h1'
    _ = k * ξ + k * (ξ * (2 * (r * ε))) := by ring
    _ < k * ξ + k * (scale / 2) := by
        have := mul_lt_mul_of_pos_left hsmall hkR
        linarith
    _ = (ξ + scale / 2) * k := by ring


/-- Exact public statement of NativeHalfBinomial.upper_estimate_scaled. -/
theorem native_upper_estimate_scaled {U Y r k c a J : ℕ} (hU : 1 ≤ U) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hJ : J = 2 * r + 1) (hA : 1 < a + 2) (ha : a = Y * (U + 1))
    (hP : 1 < 2 * (U * Y ^ 2) + 1) (hc : c = ψ hA J) (hk : k = ψ hP (r + 1))
    (hξY' : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < 2 * (Y + 1))
    (h72 : 72 * r < U + 1) (h16 : 16 ≤ Y * (U + 1)) :
    (c : ℝ) / k < ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r + 1 := by
  simpa using upper_estimate_budget (by norm_num : (0 : ℝ) < 2)
    hU hY hr hJ hA ha hP hc hk hξY' h72 h16

/-- Exact public statement of Jones1980.Ratio90.upper_estimate'.
The original unused premise hYr is retained in this compatibility wrapper. -/
theorem ordinary_upper_estimate {U Y r k c a J : ℕ} (hU : 1 ≤ U) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hJ : J = 2 * r + 1) (hA : 1 < a + 2) (ha : a = Y * (U + 1))
    (hP : 1 < 2 * (U * Y ^ 2) + 1) (hc : c = ψ hA J) (hk : k = ψ hP (r + 1))
    (hξY' : ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r < Y + 1)
    (h72 : 72 * r < U + 1) (hYr : U ^ r ≤ Y) (h16 : 16 ≤ Y * (U + 1)) :
    (c : ℝ) / k < ((U : ℝ) + 1) ^ (2 * r) / (U : ℝ) ^ r + 1 / 2 := by
  exact upper_estimate_budget (by norm_num : (0 : ℝ) < 1)
    hU hY hr hJ hA ha hP hc hk (by simpa using hξY') h72 h16

/-- Exact public statement of NativePellPower.lower_key. -/
theorem native_lower_key {X Y : ℕ} (hX : 1 ≤ X) (hY : 1 ≤ Y) :
    2 * (2 * (X * Y ^ 2) + 1) * (X + 1) ^ 2 <
      (2 * (Y * (X + 1) + 2) - 1) ^ 2 * X :=
  Jones1980.Ratio90.lower_key hX hY

/-- Exact public statement of NativePellPower.doubled_ratio_lower. -/
theorem native_doubled_ratio_lower {X Y r k c a R : ℕ}
    (hX : 1 ≤ X) (hY : 1 ≤ Y) (hr : 1 ≤ r)
    (hR : R = 2 * r + 1) (ha : a = Y * (X + 1))
    (hc : c = yn (by omega : 1 < a + 2) R)
    (hk : k = 2 * yn (by nlinarith : 1 < 2 * (X * Y ^ 2) + 1) (r + 1)) :
    k * (X + 1) ^ (2 * r) < 2 * c * X ^ r := by
  have h := Jones1980.Ratio90.lower_estimate hX hY hr hR (by omega) ha
    (by nlinarith) hc rfl
  rw [hk]
  simpa only [mul_assoc] using Nat.mul_lt_mul_of_pos_left h (by decide : 0 < 2)

#print axioms upper_estimate_budget
#print axioms native_upper_estimate_scaled
#print axioms ordinary_upper_estimate
#print axioms native_doubled_ratio_lower
end NewSimplifications
