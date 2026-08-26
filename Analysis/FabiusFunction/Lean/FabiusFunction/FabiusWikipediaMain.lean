import FabiusFunction.FabiusSharpLambertMain

/-!
# Corrected and uncorrected compact Lambert-W main terms

The source formula is most compact in the lower real Lambert-W coordinate.  The
online expression omits the centered periodic correction, so this module names
both its nonperiodic logarithmic main and the corrected main.  Their exact
decomposition isolates the missing term, while the existing saddle identity
proves that the corrected expression is the canonical Lambert-coordinate main.
-/

set_option autoImplicit false

namespace Fabius

/-- Logarithmic form, on the positive lower-Lambert branch domain, of the
compact nonperiodic expression printed in the online source.

The definition is totalized together with `Real.log` and `lowerLambertW`; the
small-positive-argument theorems use it only on its natural asymptotic domain. -/
noncomputable def fabiusWikipediaLambertMain (x : ℝ) : ℝ :=
  let W := lowerLambertW (-(Real.log 2 * x));
  -7 * Real.log 2 / 12 - Real.log (Real.pi * x) / 2 +
    (gammaZetaConstant - W - W ^ 2 / 2) / Real.log 2

/-- The literal multiplicative Lambert-W expression printed in the online
source.

The exponent `(7 / 12 : ℝ)` is deliberately a real power.  As with
`fabiusWikipediaLambertMain`, this definition is totalized, but its source
interpretation is on the positive lower-Lambert branch domain. -/
noncomputable def fabiusWikipediaLambertFactor (x : ℝ) : ℝ :=
  let W := lowerLambertW (-(Real.log 2 * x));
  1 / ((2 : ℝ) ^ (7 / 12 : ℝ) * Real.sqrt (Real.pi * x)) *
    Real.exp
      ((firstStieltjesConstant +
            Real.eulerMascheroniConstant ^ 2 / 2 - Real.pi ^ 2 / 12 -
            W - W ^ 2 / 2) /
        Real.log 2)

/-- Corrected compact form of the Wikipedia small-argument main term. -/
noncomputable def fabiusCorrectedWikipediaMain (x : ℝ) : ℝ :=
  let W := lowerLambertW (-(Real.log 2 * x));
  -7 * Real.log 2 / 12 - Real.log (Real.pi * x) / 2 +
    (gammaZetaConstant - W - W ^ 2 / 2) / Real.log 2 +
      negativeLaplacePsi (fabiusLambertPhase x)

/-- The corrected compact main is exactly the online nonperiodic main plus the
centered periodic correction at the exact lower-Lambert phase. -/
theorem fabiusCorrectedWikipediaMain_eq_WikipediaLambertMain_add (x : ℝ) :
    fabiusCorrectedWikipediaMain x =
      fabiusWikipediaLambertMain x +
        negativeLaplacePsi (fabiusLambertPhase x) := by
  rfl

/-- On the positive half-line, exponentiating the compact logarithmic main
term gives exactly the literal multiplicative expression printed online. -/
theorem exp_fabiusWikipediaLambertMain_eq_WikipediaLambertFactor
    {x : ℝ} (hx : 0 < x) :
    Real.exp (fabiusWikipediaLambertMain x) =
      fabiusWikipediaLambertFactor x := by
  have hpix : 0 < Real.pi * x := mul_pos Real.pi_pos hx
  have htwo :
      Real.exp (-7 * Real.log 2 / 12) =
        ((2 : ℝ) ^ (7 / 12 : ℝ))⁻¹ := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2),
      ← Real.exp_neg]
    congr 1
    ring
  have hsqrt :
      Real.exp (Real.log (Real.pi * x) / 2) =
        Real.sqrt (Real.pi * x) := by
    rw [← Real.log_sqrt hpix.le,
      Real.exp_log (Real.sqrt_pos.2 hpix)]
  have hgamma :
      gammaZetaConstant =
        firstStieltjesConstant +
          Real.eulerMascheroniConstant ^ 2 / 2 - Real.pi ^ 2 / 12 := by
    unfold gammaZetaConstant
    ring
  unfold fabiusWikipediaLambertMain fabiusWikipediaLambertFactor
  dsimp only
  rw [hgamma, Real.exp_add, Real.exp_sub, htwo, hsqrt]
  simp only [div_eq_mul_inv, mul_inv_rev]
  ring

/-- The literal online factor is strictly positive on its intended positive
domain. -/
theorem fabiusWikipediaLambertFactor_pos {x : ℝ} (hx : 0 < x) :
    0 < fabiusWikipediaLambertFactor x := by
  rw [← exp_fabiusWikipediaLambertMain_eq_WikipediaLambertFactor hx]
  exact Real.exp_pos _

/-- Exponentiating the corrected logarithmic main multiplies the literal
online factor by the missing periodic correction. -/
theorem
    exp_fabiusCorrectedWikipediaMain_eq_WikipediaLambertFactor_mul_periodic
    {x : ℝ} (hx : 0 < x) :
    Real.exp (fabiusCorrectedWikipediaMain x) =
      fabiusWikipediaLambertFactor x *
        Real.exp (negativeLaplacePsi (fabiusLambertPhase x)) := by
  rw [fabiusCorrectedWikipediaMain_eq_WikipediaLambertMain_add,
    Real.exp_add,
    exp_fabiusWikipediaLambertMain_eq_WikipediaLambertFactor hx]

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
