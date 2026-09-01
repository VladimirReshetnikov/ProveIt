import FabiusFunction.HeineTransformation

/-!
# The q-Gauss summation

Specializing Heine's transformation to `z = c/(ab)` makes `az = c/b` equal to
the denominator parameter of the transformed series, which therefore collapses
to the `q`-binomial series `₁φ₀(c/(ab); –; q, b) = (c/a;q)_∞/(b;q)_∞`.  This is
the **`q`-Gauss summation**

`₂φ₁(a, b; c; q, c/(ab)) = (c/a;q)_∞ (c/b;q)_∞ / ((c;q)_∞ (c/(ab);q)_∞)`,

here on the domain `‖b‖ < 1`, `‖c/(ab)‖ < 1` where Heine's transformation is
available, with `a, b ≠ 0` and nonvanishing `(c;q)_∞`, `(c/b;q)_∞`.

## Main declarations

* `twoPhiOne_self_eq`: `₂φ₁(a, b; a; q, z) = (bz;q)_∞/(z;q)_∞`.
* `q_gauss_summation`: the `q`-Gauss sum.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Fabius

variable {𝕜 : Type*} [NormedField 𝕜] [CompleteSpace 𝕜]

/-- When a numerator parameter equals the denominator parameter, `₂φ₁` is the
`q`-binomial series: `₂φ₁(a, b; a; q, z) = (bz;q)_∞/(z;q)_∞`. -/
theorem twoPhiOne_self_eq {q : 𝕜} (hq : ‖q‖ < 1) {a : 𝕜} (ha : qPochhammerInfIn a q ≠ 0)
    (b : 𝕜) {z : 𝕜} (hz : ‖z‖ < 1) :
    twoPhiOne a b a q z = qPochhammerInfIn (b * z) q / qPochhammerInfIn z q := by
  have han := finiteQPochhammerIn_ne_zero_of_qPochhammerInfIn_ne_zero a hq ha
  refine ((hasSum_qBinomial_theorem hq b hz).congr_fun fun n => ?_).tsum_eq
  rw [twoPhiOneTerm, mul_comm (finiteQPochhammerIn a q n), mul_div_mul_right _ _ (han n)]

/-- **The `q`-Gauss summation**
`₂φ₁(a, b; c; q, c/(ab)) = (c/a;q)_∞ (c/b;q)_∞ / ((c;q)_∞ (c/(ab);q)_∞)`, on the
domain `‖b‖ < 1`, `‖c/(ab)‖ < 1`, for `a, b ≠ 0` and nonvanishing `(c;q)_∞`,
`(c/b;q)_∞`. -/
theorem q_gauss_summation {q : 𝕜} (hq : ‖q‖ < 1) {a b c : 𝕜} (ha0 : a ≠ 0) (hb0 : b ≠ 0)
    (hb : ‖b‖ < 1) (hc : qPochhammerInfIn c q ≠ 0) (hcb : qPochhammerInfIn (c / b) q ≠ 0)
    (hz : ‖c / (a * b)‖ < 1) :
    twoPhiOne a b c q (c / (a * b)) =
      qPochhammerInfIn (c / a) q * qPochhammerInfIn (c / b) q /
        (qPochhammerInfIn c q * qPochhammerInfIn (c / (a * b)) q) := by
  have haz : a * (c / (a * b)) = c / b := by
    rw [mul_div_assoc', mul_div_mul_left c b ha0]
  have hzb : c / (a * b) * b = c / a := by
    rw [div_mul_eq_mul_div, mul_div_mul_right c a hb0]
  have hbinf : qPochhammerInfIn b q ≠ 0 := qPochhammerInfIn_ne_zero_of_norm_lt_one hq hb
  have hzinf : qPochhammerInfIn (c / (a * b)) q ≠ 0 :=
    qPochhammerInfIn_ne_zero_of_norm_lt_one hq hz
  rw [heine_transformation hq a hb0 hb hc hz (by rw [haz]; exact hcb), haz,
    twoPhiOne_self_eq hq hcb (c / (a * b)) hb, hzb, div_mul_div_comm,
    div_eq_div_iff (mul_ne_zero (mul_ne_zero hc hzinf) hbinf) (mul_ne_zero hc hzinf)]
  ring

end Fabius
