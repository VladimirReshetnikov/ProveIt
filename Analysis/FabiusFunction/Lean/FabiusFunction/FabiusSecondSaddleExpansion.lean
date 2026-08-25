import FabiusFunction.FabiusFullAsymptoticExpansion
import FabiusFunction.FabiusSecondSaddleCorrection

/-!
# The small-argument expansion through order `lambda⁻²`

`FabiusFullAsymptoticExpansion` proves that for every `N` the logarithm of the
Fabius function differs from `fabiusSharpLambertMain` plus its first `N`
periodic corrections by `O(lambda⁻ᴺ)`, and identifies the truncation at `N = 2`
as the sharp main term plus `fabiusFirstSaddleCorrection / lambda`.  At that
point the next coefficient was known only as the output of a recursion.

`FabiusSecondSaddleCorrection` computes it.  This module substitutes the result
into the truncation at `N = 3`, giving the source-facing statement

```text
log F(x) = fabiusSharpLambertMain x
  + fabiusFirstSaddleCorrection (fabiusLambertPhase x) / fabiusLambertPhase x
  + fabiusSecondSaddleCorrection (fabiusLambertPhase x) / fabiusLambertPhase x ^ 2
  + O (fabiusLambertPhase x ⁻¹ ^ 3),
```

with both correction terms written out in closed form.  As in the order-two
case the theorems identify the coefficient functions; they do not assert that
either function is nowhere zero.

The weaker remainder `O((-log x)⁻³)` is also recorded, since that is the rate a
reader arriving from the elementary `log x` / `log (-log x)` formulas expects.
The periodic coefficients still use the exact Lambert phase: substituting an
expansion of the phase into them would need a separate all-order composition
theorem, which is deliberately not claimed here.
-/

set_option autoImplicit false

open Filter Set Asymptotics

namespace Fabius

noncomputable section

/-- The first three logarithmic saddle coefficients at the exact Lambert phase.
The zeroth vanishes, so the partial sum is the two explicit corrections. -/
theorem fabiusSaddleLogPartialSum_three (lam : ℝ) :
    fabiusSaddleLogPartialSum 3 lam =
      fabiusFirstSaddleCorrection lam / lam +
        fabiusSecondSaddleCorrection lam / lam ^ 2 := by
  rw [fabiusSaddleLogPartialSum, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one, fabiusSaddleLogCoefficient_zero,
    fabiusSaddleLogCoefficient_one_eq_firstSaddleCorrection,
    fabiusSaddleLogCoefficient_two_eq_secondSaddleCorrection]
  ring

/-- The order-three expansion is the sharp main term plus the two explicit
periodic corrections. -/
theorem fabiusSharpLambertExpansion_three (x : ℝ) :
    fabiusSharpLambertExpansion 3 x =
      fabiusSharpLambertMain x +
        (fabiusFirstSaddleCorrection (fabiusLambertPhase x) /
            fabiusLambertPhase x +
          fabiusSecondSaddleCorrection (fabiusLambertPhase x) /
            fabiusLambertPhase x ^ 2) := by
  rw [fabiusSharpLambertExpansion, fabiusSaddleLogPartialSum_three]

/-- **The small-argument expansion through order `lambda⁻²`, written out.** -/
theorem log_fabius_sub_twoSaddleCorrections_isBigO
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => Real.log (fabiusReal F x) - fabiusSharpLambertMain x -
        (fabiusFirstSaddleCorrection (fabiusLambertPhase x) /
            fabiusLambertPhase x +
          fabiusSecondSaddleCorrection (fabiusLambertPhase x) /
            fabiusLambertPhase x ^ 2)) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => (fabiusLambertPhase x)⁻¹ ^ 3) := by
  have h := log_fabius_sub_sharpLambertExpansion_isBigO F hF 3
  apply h.congr_left
  intro x
  rw [fabiusSharpLambertExpansion_three]
  ring

/-- The same statement with the remainder weakened to the literal
inverse-logarithmic rate. -/
theorem log_fabius_sub_twoSaddleCorrections_isBigO_negLog
    (F : BoundedFabius) (hF : IsFabius F) :
    (fun x : ℝ => Real.log (fabiusReal F x) - fabiusSharpLambertMain x -
        (fabiusFirstSaddleCorrection (fabiusLambertPhase x) /
            fabiusLambertPhase x +
          fabiusSecondSaddleCorrection (fabiusLambertPhase x) /
            fabiusLambertPhase x ^ 2)) =O[nhdsWithin 0 (Ioi 0)]
      (fun x : ℝ => (-Real.log x)⁻¹ ^ 3) := by
  have h := log_fabius_sub_sharpLambertExpansion_isBigO_negLog F hF 3
  apply h.congr_left
  intro x
  rw [fabiusSharpLambertExpansion_three]
  ring

end

end Fabius
