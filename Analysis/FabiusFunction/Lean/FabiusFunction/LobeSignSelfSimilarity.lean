import FabiusFunction.ThueMorseLobeSign
import FabiusFunction.DyadicClosedForm

/-!
# Self-similarity of the lobe-sign pattern

The Thue–Morse identification of `ThueMorseLobeSign` transports the
substitution rules `w(2m) = w(m)`, `w(2m+1) = w(m)+1` — already
available as `thueMorseSign_two_mul` and
`thueMorseSign_two_mul_add_one` — to `Φ` itself: doubling the lobe
index preserves the sign of `Φ`, and the odd neighbour reverses it.

`sign Φ|_(2m,2m+1) = sign Φ|_(m,m+1)`,
`sign Φ|_(2m+1,2m+2) = − sign Φ|_(m,m+1)`.

Sign comparisons are stated multiplicatively, `Φ(x)‖Φ(y)‖ =
±Φ(y)‖Φ(x)‖`, so no division or positivity side condition is needed.

* `lobe_sign_two_mul` — doubling preserves the sign.
* `lobe_sign_two_mul_add_one` — the odd neighbour flips it.
-/

set_option autoImplicit false

open Filter Topology Real Set

namespace Fabius

/-- **Doubling the lobe index preserves the sign of `Φ`.** -/
theorem lobe_sign_two_mul {m : ℕ} {x y : ℝ}
    (hx : x ∈ Set.Ioo ((2 * m : ℕ) : ℝ) (((2 * m : ℕ) : ℝ) + 1))
    (hy : y ∈ Set.Ioo ((m : ℕ) : ℝ) (((m : ℕ) : ℝ) + 1)) :
    rvachevFourierProduct (x : ℂ) *
        (‖rvachevFourierProduct (y : ℂ)‖ : ℂ) =
      rvachevFourierProduct (y : ℂ) *
        (‖rvachevFourierProduct (x : ℂ)‖ : ℂ) := by
  -- freeze the moduli first, so the sign rewrites cannot re-enter them
  set a : ℝ := ‖rvachevFourierProduct (x : ℂ)‖ with ha
  set b : ℝ := ‖rvachevFourierProduct (y : ℂ)‖ with hb
  have hxe := rvachevFourierProduct_eq_thueMorse_sign_mul_norm hx
  have hye := rvachevFourierProduct_eq_thueMorse_sign_mul_norm hy
  rw [hxe, hye, thueMorseSign_two_mul]
  push_cast
  ring

/-- **The odd neighbour reverses the sign of `Φ`.** -/
theorem lobe_sign_two_mul_add_one {m : ℕ} {x y : ℝ}
    (hx : x ∈ Set.Ioo ((2 * m + 1 : ℕ) : ℝ)
      (((2 * m + 1 : ℕ) : ℝ) + 1))
    (hy : y ∈ Set.Ioo ((m : ℕ) : ℝ) (((m : ℕ) : ℝ) + 1)) :
    rvachevFourierProduct (x : ℂ) *
        (‖rvachevFourierProduct (y : ℂ)‖ : ℂ) =
      -(rvachevFourierProduct (y : ℂ) *
        (‖rvachevFourierProduct (x : ℂ)‖ : ℂ)) := by
  set a : ℝ := ‖rvachevFourierProduct (x : ℂ)‖ with ha
  set b : ℝ := ‖rvachevFourierProduct (y : ℂ)‖ with hb
  have hxe := rvachevFourierProduct_eq_thueMorse_sign_mul_norm hx
  have hye := rvachevFourierProduct_eq_thueMorse_sign_mul_norm hy
  rw [hxe, hye, thueMorseSign_two_mul_add_one]
  push_cast
  ring

end Fabius
