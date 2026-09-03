import FabiusFunction.EffectiveGapInverse
import FabiusFunction.FabiusComputableSpline
import FabiusFunction.FabiusInverseEffectiveContinuity

/-!
# The Fabius instance of gap-certified effective inversion

`EffectiveGapInverse` shows abstractly that a computable positive rational
lower bound for every dyadic forward gap of a strictly increasing bijection
of `[0,1]` already makes its inverse sequentially computable, effectively
uniformly continuous, and — after clamping — a total computable real
function.  This module supplies the Fabius instance of that hypothesis, so
the abstract theorems apply to `fabiusInv`.

The gap certificate is the reciprocal of the factorial denominator of
`FabiusInverseEffectiveContinuity`: for `x` in `[0, 1 - 2⁻ᵖ]`,

`1 / D(p) ≤ F(2⁻ᵖ) ≤ F(x + 2⁻ᵖ) - F(x)`,

the first inequality being `inv_inverseFabiusFactorialDenominator_le_fabiusReal`
and the second the denominator-free superadditivity
`fabiusReal_sub_le_sub`.  Note that only the gap at the *left* endpoint has
to be certified: superadditivity moves it to every position.

* `fabiusGapSequence` — the certificate `p ↦ 1/D(p)` as a computable
  positive rational sequence.
* `fabiusReal_gap_le` — the gap bound at every position.
* `fabiusInv_effectiveInversionOn_Icc` — sequential computability and
  effective uniform continuity of `fabiusInv` on `[0,1]`, from the gap
  certificate alone.
* `fabiusInv_unitClamp_isComputableRealFunction_of_gap` — the clamped
  inverse as a total computable real function.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- The Fabius dyadic-gap certificate: `1 / D(p)`, with `D` the factorial
denominator of `FabiusInverseEffectiveContinuity`. -/
def fabiusGapSequence : ComputablePositiveRationalSequence where
  numerator := fun _ => 1
  denominator := inverseFabiusFactorialDenominator
  numerator_computable := Computable.const 1
  denominator_computable := inverseFabiusFactorialDenominator_primrec.to_comp
  numerator_pos := fun _ => Nat.one_pos
  denominator_pos := fun p => by
    rw [inverseFabiusFactorialDenominator_eq]
    positivity

/-- The value of the Fabius gap certificate is the reciprocal of the
factorial denominator. -/
theorem fabiusGapSequence_value (p : ℕ) :
    fabiusGapSequence.value p =
      ((inverseFabiusFactorialDenominator p : ℝ))⁻¹ := by
  rw [ComputablePositiveRationalSequence.value]
  show ((1 : ℕ) : ℝ) / (inverseFabiusFactorialDenominator p : ℝ) = _
  rw [Nat.cast_one, one_div]

/-- **The dyadic forward gaps of the Fabius function are uniformly bounded
below by the factorial certificate**: for every `p` and every
`x ∈ [0, 1 - 2⁻ᵖ]`,

`1 / D(p) ≤ F(x + 2⁻ᵖ) - F(x)`.

Only the gap at the left endpoint is certified analytically; the
superadditivity `F(b - a) ≤ F(b) - F(a)` moves it to every position. -/
theorem fabiusReal_gap_le (F : BoundedFabius) (hF : IsFabius F) (p : ℕ)
    {x : ℝ} (hx : x ∈ Icc (0 : ℝ) (1 - ((2 : ℝ) ^ p)⁻¹)) :
    fabiusGapSequence.value p ≤
      fabiusReal F (x + ((2 : ℝ) ^ p)⁻¹) - fabiusReal F x := by
  have hstep0 : (0 : ℝ) < ((2 : ℝ) ^ p)⁻¹ := by positivity
  have hstep1 : ((2 : ℝ) ^ p)⁻¹ ≤ 1 :=
    (inv_le_one₀ (by positivity)).2 (one_le_pow₀ (by norm_num))
  have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1, by linarith [hx.2]⟩
  have hyIcc : x + ((2 : ℝ) ^ p)⁻¹ ∈ Icc (0 : ℝ) 1 :=
    ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hsuper := fabiusReal_sub_le_sub F hF hxIcc hyIcc
    (by linarith : x ≤ x + ((2 : ℝ) ^ p)⁻¹)
  rw [show x + ((2 : ℝ) ^ p)⁻¹ - x = ((2 : ℝ) ^ p)⁻¹ by ring] at hsuper
  rw [fabiusGapSequence_value]
  exact (inv_inverseFabiusFactorialDenominator_le_fabiusReal F hF p).trans
    hsuper

/-- **Gap-certified effective inversion for the Fabius function**: the
totalized inverse is sequentially computable and effectively uniformly
continuous on `[0,1]`, deduced from the dyadic gap certificate alone
through the abstract theorem of `EffectiveGapInverse`. -/
theorem fabiusInv_effectiveInversionOn_Icc
    (F : BoundedFabius) (hF : IsFabius F) :
    SequentiallyComputableOn (fabiusInv F hF) (Icc (0 : ℝ) 1) ∧
      EffectivelyUniformContinuousOn (fabiusInv F hF) (Icc (0 : ℝ) 1) :=
  effectiveInversionOn_Icc_of_computablePositiveRationalGap
    (fabiusHasComputableDyadicApproximation F hF)
    (strictMonoOn_fabiusReal F hF)
    (fun x _ => ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩)
    (fun u _ => fabiusInv_mem_Icc F hF u)
    ⟨fun x hx => fabiusInv_fabiusReal F hF hx,
      fun y hy => fabiusReal_fabiusInv F hF hy⟩
    fabiusGapSequence (fun p _x hx => fabiusReal_gap_le F hF p hx)

/-- **The clamped Fabius inverse is a total computable real function**,
obtained from the gap certificate through the abstract packaging of
`EffectiveGapInverse`.  This is a second, gap-based route to
`FabiusInverseComputable.fabiusInv_isComputableRealFunction`. -/
theorem fabiusInv_unitClamp_isComputableRealFunction_of_gap
    (F : BoundedFabius) (hF : IsFabius F) :
    IsComputableRealFunction (fun x => fabiusInv F hF (unitClamp x)) :=
  clampedEffectiveInversion_of_computablePositiveRationalGap
    (fabiusHasComputableDyadicApproximation F hF)
    (strictMonoOn_fabiusReal F hF)
    (fun x _ => ⟨fabiusReal_nonneg F x, fabiusReal_le_one F x⟩)
    (fun u _ => fabiusInv_mem_Icc F hF u)
    ⟨fun x hx => fabiusInv_fabiusReal F hF hx,
      fun y hy => fabiusReal_fabiusInv F hF hy⟩
    fabiusGapSequence (fun p _x hx => fabiusReal_gap_le F hF p hx)

end Fabius
