import FabiusFunction.ThueMorseInfiniteProduct
import FabiusFunction.ThueMorseBinomialLog

/-!
# The base-`b` products for the Thue–Morse constant

The atlas's `p1:cor:base-b-product`: for every real `b > 1`, the signed
Thue–Morse series and the Thue–Morse bit series in base `b` are

`∑_{n ≥ 0} ε_n / b^{n+1} = (1/b) ∏_{j ≥ 0} (1 - b^{-2^j})`,

`Θ_b = ∑_{n ≥ 0} t_n / b^{n+1} = 1 / (2(b-1)) - (1/(2b)) ∏_{j ≥ 0} (1 - b^{-2^j})`.

Both are the real infinite product `tsum_thueMorseSign_mul_pow` at
`x = 1/b`, the second after writing the bit as `t_n = (1 - ε_n)/2` and
summing the geometric series.  At `b = 2` the second display is the
classical binary expansion of the Thue–Morse constant `Θ_2 = 0.0110100110…₂`.

## Main declarations

* `tsum_thueMorseSign_div_pow_succ` — **`p1:eq:signed-base-b`**.
* `tsum_thueMorseBit_div_pow_succ` — **`p1:eq:base-b-product`**.
-/

set_option autoImplicit false

namespace Fabius

/-- `|1/b| < 1` for `b > 1`. -/
theorem abs_inv_lt_one_of_one_lt {b : ℝ} (hb : 1 < b) : |b⁻¹| < 1 := by
  have hb0 : (0 : ℝ) < b := by linarith
  rw [abs_of_pos (inv_pos.mpr hb0)]
  exact (inv_lt_one₀ hb0).mpr hb

/-- **`p1:eq:signed-base-b`**: `∑ ε_n / b^{n+1} = (1/b) ∏ (1 - b^{-2^j})` for
real `b > 1`. -/
theorem tsum_thueMorseSign_div_pow_succ {b : ℝ} (hb : 1 < b) :
    ∑' n : ℕ, (thueMorseSign n : ℝ) / b ^ (n + 1)
      = b⁻¹ * ∏' j : ℕ, (1 - b⁻¹ ^ (2 ^ j)) := by
  rw [← tsum_thueMorseSign_mul_pow (abs_inv_lt_one_of_one_lt hb), ← tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [div_eq_mul_inv, pow_succ, mul_inv, ← inv_pow]
  ring

/-- **`p1:eq:base-b-product`**: the Thue–Morse bit series in base `b > 1`,
`Θ_b = ∑ t_n / b^{n+1} = 1/(2(b-1)) - (1/(2b)) ∏ (1 - b^{-2^j})`. -/
theorem tsum_thueMorseBit_div_pow_succ {b : ℝ} (hb : 1 < b) :
    ∑' n : ℕ, (thueMorseBit n : ℝ) / b ^ (n + 1)
      = 1 / (2 * (b - 1)) - 1 / (2 * b) * ∏' j : ℕ, (1 - b⁻¹ ^ (2 ^ j)) := by
  have hx : |b⁻¹| < 1 := abs_inv_lt_one_of_one_lt hb
  have hsum : Summable (fun n : ℕ => (thueMorseSign n : ℝ) * b⁻¹ ^ n) :=
    summable_thueMorseSign_mul_pow hx
  have hgeo : Summable (fun n : ℕ => b⁻¹ ^ n) := summable_geometric_of_abs_lt_one hx
  have hterm : ∀ n : ℕ, (thueMorseBit n : ℝ) / b ^ (n + 1)
      = b⁻¹ * ((1 / 2) * b⁻¹ ^ n - (1 / 2) * ((thueMorseSign n : ℝ) * b⁻¹ ^ n)) := by
    intro n
    have hR : (thueMorseSign n : ℝ) = 1 - 2 * (thueMorseBit n : ℝ) := by
      exact_mod_cast thueMorseSign_eq_one_sub_two_mul_bit n
    rw [hR, div_eq_mul_inv, pow_succ, mul_inv, ← inv_pow]
    ring
  simp_rw [hterm]
  rw [tsum_mul_left, (hgeo.mul_left _).tsum_sub (hsum.mul_left _), tsum_mul_left, tsum_mul_left,
    tsum_geometric_of_abs_lt_one hx, tsum_thueMorseSign_mul_pow hx]
  have hb0 : b ≠ 0 := by linarith
  have hb1 : b - 1 ≠ 0 := by linarith
  have hb2 : 1 - b⁻¹ ≠ 0 := by
    have : b⁻¹ < 1 := (inv_lt_one₀ (by linarith)).mpr hb
    linarith
  field_simp

end Fabius
