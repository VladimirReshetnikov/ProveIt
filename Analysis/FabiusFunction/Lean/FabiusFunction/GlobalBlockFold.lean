import FabiusFunction.GlobalDyadic
import FabiusFunction.DyadicClosedForm

/-!
# The global block fold of the signed evaluator

The umbrella gap register's *Global block fold for the signed
evaluator* candidate displays the triangular block reduction behind
`extendedFabiusDyadicValue`: writing `a = 2sB + R` with `s = 2^n` and
`0 ≤ R < 2s`, and folding `C = R` or `C = 2s - R` according to the
half of the period, the signed extension satisfies

`ℱ(a/2^n) = (-1)^{wt(B)} · F(C/2^n)`  with  `0 ≤ C ≤ s`.

The executable definition performs exactly this quotient–remainder
fold, but the register records that no public theorem states it with
these variables and hypotheses.  This module packages it at both
levels: the executable identity about `extendedFabiusDyadicValue`
itself, and — composed with `extendedFabiusDyadicValue_cast`,
`fabiusDyadicUnit_eq_fabiusDyadic`, and `fabiusDyadic_cast` — the
displayed analytic formula, for every bounded Fabius function.

* `blockFoldCore_le` — the folded numerator stays in the unit block.
* `extendedFabiusDyadicValue_block_fold` — the executable fold with
  the register's explicit decomposition hypotheses.
* `extendedFabius_block_fold` — the analytic triangular block
  reduction `ℱ(a/2^n) = (-1)^{wt(B)}·F(C/2^n)`.
-/

set_option autoImplicit false

namespace Fabius

/-- The folded core numerator of the triangular block reduction stays
in the unit block: `C ≤ 2^n`. -/
theorem blockFoldCore_le (n R : ℕ) (hR : R < 2 * 2 ^ n) :
    (if R ≤ 2 ^ n then R else 2 * 2 ^ n - R) ≤ 2 ^ n := by
  split_ifs with h
  · exact h
  · omega

/-- **The executable block fold, packaged** with the register's
explicit quotient–remainder hypotheses: for `a = 2·2^n·B + R` with
`0 < a` and `R < 2·2^n`, the signed evaluator is the Thue–Morse block
sign times the unit evaluator at the folded numerator. -/
theorem extendedFabiusDyadicValue_block_fold (n : ℕ) {a B R : ℕ}
    (ha : 0 < a) (hdecomp : a = 2 * 2 ^ n * B + R) (hR : R < 2 * 2 ^ n) :
    extendedFabiusDyadicValue n (a : ℤ) =
      (thueMorseSign B : ℚ) *
        fabiusDyadicUnit n (if R ≤ 2 ^ n then R else 2 * 2 ^ n - R) := by
  have hper : 0 < 2 * 2 ^ n := by positivity
  have hdiv : a / (2 * 2 ^ n) = B := by
    rw [hdecomp, Nat.mul_add_div hper, Nat.div_eq_of_lt hR, Nat.add_zero]
  have hmod : a % (2 * 2 ^ n) = R := by
    rw [hdecomp, Nat.mul_add_mod, Nat.mod_eq_of_lt hR]
  rw [extendedFabiusDyadicValue, if_neg (by omega)]
  simp only [Int.toNat_natCast]
  rw [hdiv, hmod]

/-- **The triangular block reduction** (the register's candidate): for
every bounded Fabius function and every numerator decomposed
as `a = 2·2^n·B + R` with `R < 2·2^n` (positivity of `a` is not needed:
at `a = 0` both sides vanish),

`ℱ(a/2^n) = (-1)^{wt(B)} · F(C/2^n)`

with the folded numerator `C = R` on the first half-period and
`C = 2·2^n - R` on the second, so that `0 ≤ C ≤ 2^n`
(`blockFoldCore_le`). -/
theorem extendedFabius_block_fold_of_decomp (F : BoundedFabius)
    (hF : IsFabius F) (n : ℕ) {a B R : ℕ}
    (hdecomp : a = 2 * 2 ^ n * B + R) (hR : R < 2 * 2 ^ n) :
    extendedFabius F ((a : ℝ) / 2 ^ n) =
      (thueMorseSign B : ℝ) *
        fabiusReal F
          ((↑(if R ≤ 2 ^ n then R else 2 * 2 ^ n - R) : ℝ) / 2 ^ n) := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · -- `a = 0` forces `B = R = 0`, and both sides vanish
    have hR0 : R = 0 := by omega
    have hB0 : 2 * 2 ^ n * B = 0 := by omega
    have hB : B = 0 := by
      rcases Nat.mul_eq_zero.mp hB0 with h | h
      · exact absurd h (by positivity)
      · exact h
    subst hR0 hB
    simp [extendedFabius_zero F hF, hF.zero_of_nonpos 0 le_rfl,
      thueMorseSign, binaryWeight]
  · have hcast := extendedFabiusDyadicValue_cast F hF n (a : ℤ)
    rw [show (((a : ℤ) : ℝ)) = (a : ℝ) by push_cast; ring] at hcast
    rw [← hcast, extendedFabiusDyadicValue_block_fold n ha hdecomp hR]
    push_cast
    rw [fabiusDyadicUnit_eq_fabiusDyadic n _ (blockFoldCore_le n R hR),
      fabiusDyadic_cast F hF n _ (blockFoldCore_le n R hR)]
    push_cast
    ring

/-- The triangular block reduction with the register's positivity
hypothesis, an instance of `extendedFabius_block_fold_of_decomp`. -/
theorem extendedFabius_block_fold (F : BoundedFabius) (hF : IsFabius F)
    (n : ℕ) {a B R : ℕ} (_ha : 0 < a)
    (hdecomp : a = 2 * 2 ^ n * B + R) (hR : R < 2 * 2 ^ n) :
    extendedFabius F ((a : ℝ) / 2 ^ n) =
      (thueMorseSign B : ℝ) *
        fabiusReal F
          ((↑(if R ≤ 2 ^ n then R else 2 * 2 ^ n - R) : ℝ) / 2 ^ n) :=
  extendedFabius_block_fold_of_decomp F hF n hdecomp hR

end Fabius
