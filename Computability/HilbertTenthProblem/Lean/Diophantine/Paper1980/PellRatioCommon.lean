import Diophantine.Paper1980.PellDoubled
import Diophantine.Paper1982.Ratio

/-! Elementary bounds shared by the ratio blocks of the 99- and 90-operation systems
(`PellRatio`, `PellRatio90`). They live in their own namespace and are
re-exported by those two modules, so no other module sees new names. -/

namespace Jones1980.RatioCommon

open Diophantine Pell

/-- `(1 + ε)^r ≤ 1 + 2rε` for `0 ≤ ε` with `rε ≤ 1/2`. -/
theorem one_add_pow_le {ε : ℝ} (r : ℕ) (hε : 0 ≤ ε) (hrε : (r : ℝ) * ε ≤ 1 / 2) :
    (1 + ε) ^ r ≤ 1 + 2 * (r * ε) := by
  rcases Nat.eq_zero_or_pos r with h | h
  · subst h; simp
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast h
  have hε1 : ε ≤ 1 := by nlinarith
  have h5 : (1 + ε) ^ r * (1 - ε) ^ r ≤ 1 := by
    rw [← mul_pow]
    have : (1 + ε) * (1 - ε) = 1 - ε ^ 2 := by ring
    rw [this]
    exact pow_le_one₀ (by nlinarith) (by nlinarith)
  have h2 : 1 - r * ε ≤ (1 - ε) ^ r := Jones1982.ineq_2_17_a hε1 r
  have h3 : (1 - r * ε)⁻¹ ≤ 1 + 2 * (r * ε) := Jones1982.ineq_2_17_b (by positivity) hrε
  have hpos : 0 < 1 - r * ε := by linarith
  have hpos' : 0 < (1 - ε) ^ r := lt_of_lt_of_le hpos h2
  have h4 : (1 + ε) ^ r ≤ 1 / (1 - ε) ^ r := by
    rw [le_div_iff₀ hpos']; linarith [h5]
  have h6 : 1 / (1 - ε) ^ r ≤ 1 / (1 - r * ε) := one_div_le_one_div_of_le hpos h2
  calc (1 + ε) ^ r ≤ 1 / (1 - ε) ^ r := h4
    _ ≤ 1 / (1 - r * ε) := h6
    _ = (1 - r * ε)⁻¹ := one_div _
    _ ≤ 1 + 2 * (r * ε) := h3

/-- The main parameter shift `a = Y(U+1)` exceeds `U^(r+1)` once `U^r ≤ Y`. -/
theorem a_gt {U Y r a : ℕ} (hU : 1 ≤ U) (ha : a = Y * (U + 1)) (hYr : U ^ r ≤ Y) :
    U ^ (r + 1) < a := by
  rw [ha, pow_succ]
  have h1 : U ^ r * U < U ^ r * (U + 1) := by
    have : 0 < U ^ r := by positivity
    nlinarith
  calc U ^ r * U < U ^ r * (U + 1) := h1
    _ ≤ Y * (U + 1) := Nat.mul_le_mul_right _ hYr

/-- The central-binomial divisibility `n² ∣ C(2r, r)` from `Y = C(2r,r) + wU`, `n² ∣ U`,
`n² ∣ Y`. -/
theorem central_dvd {n U Y r w : ℕ} (hU : n ^ 2 ∣ U) (hY : n ^ 2 ∣ Y)
    (h : Y = (2 * r).choose r + w * U) : n ^ 2 ∣ (2 * r).choose r := by
  have h1 : n ^ 2 ∣ w * U := Dvd.dvd.mul_left hU w
  have h2 : (2 * r).choose r = Y - w * U := by omega
  rw [h2]; exact Nat.dvd_sub hY h1

end Jones1980.RatioCommon
