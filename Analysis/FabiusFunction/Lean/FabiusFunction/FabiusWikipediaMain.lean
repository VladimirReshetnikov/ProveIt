import FabiusFunction.FabiusSharpLambertMain

/-!
# The corrected compact Wikipedia main term

The source formula is most compact in the lower real Lambert-W coordinate.
This module defines that expression, includes the centered periodic correction,
and proves that it is exactly the Lambert-coordinate saddle main term.
-/

set_option autoImplicit false

namespace Fabius

/-- Corrected compact form of the Wikipedia small-argument main term. -/
noncomputable def fabiusCorrectedWikipediaMain (x : ℝ) : ℝ :=
  let W := lowerLambertW (-(Real.log 2 * x));
  -7 * Real.log 2 / 12 - Real.log (Real.pi * x) / 2 +
    (gammaZetaConstant - W - W ^ 2 / 2) / Real.log 2 +
      negativeLaplacePsi (fabiusLambertPhase x)

/-- Logarithmic form of the exact saddle equation `λ 2⁻λ = x`. -/
theorem log_fabiusLambertArgument {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    Real.log x = Real.log (fabiusLambertPhase x) -
      Real.log 2 * fabiusLambertPhase x := by
  have hlam := fabiusLambertPhase_pos hx hsmall
  have heq : fabiusLambertPhase x *
      (2 : ℝ) ^ (-fabiusLambertPhase x) = x := by
    exact paperLambertN_eq9 hx hsmall
  calc
    Real.log x = Real.log (fabiusLambertPhase x *
        (2 : ℝ) ^ (-fabiusLambertPhase x)) := congrArg Real.log heq.symm
    _ = Real.log (fabiusLambertPhase x) +
        Real.log ((2 : ℝ) ^ (-fabiusLambertPhase x)) := by
      rw [Real.log_mul hlam.ne'
        (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).ne']
    _ = _ := by
      rw [Real.log_rpow (by norm_num : (0 : ℝ) < 2)]
      ring

/-- The compact Wikipedia/Lambert expression is exactly the saddle main term. -/
theorem fabiusCorrectedWikipediaMain_eq_sharpLambertMain
    {x : ℝ} (hx : 0 < x)
    (hsmall : Real.log 2 * x < Real.exp (-1)) :
    fabiusCorrectedWikipediaMain x = fabiusSharpLambertMain x := by
  have hL : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hlogx := log_fabiusLambertArgument hx hsmall
  have hlogpix : Real.log (Real.pi * x) = Real.log Real.pi + Real.log x := by
    rw [Real.log_mul Real.pi_ne_zero hx.ne']
  have hW : lowerLambertW (-(Real.log 2 * x)) =
      -Real.log 2 * fabiusLambertPhase x := by
    unfold fabiusLambertPhase paperLambertN
    field_simp [hL]
  unfold fabiusCorrectedWikipediaMain fabiusSharpLambertMain
  dsimp
  rw [hlogpix, hlogx, hW]
  unfold fabiusSharpAsymptoticConstant
  field_simp [hL]
  ring

end Fabius
