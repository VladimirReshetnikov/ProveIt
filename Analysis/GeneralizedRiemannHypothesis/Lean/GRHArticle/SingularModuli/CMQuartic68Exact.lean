import GRHArticle.SingularModuli.CMQuartic68Identification
import GRHArticle.SingularModuli.Prime17DiagonalChecks

/-!
# The singular moduli of discriminant −68

The exact level-17 calculation identifies the analytic class polynomial
and makes the previously checked minimum-support certificate unconditional.
-/

namespace GRHArticle.SingularModuli

/-- The analytic class polynomial at discriminant −68 is the printed integer quartic. -/
theorem analyticClassPolynomial_sixtyEight_eq_printed :
    analyticClassPolynomial 68 = quartic68Int.map (Int.castRingHom ℂ) := by
  apply analyticClassPolynomial_sixtyEight_eq_printed_of_diagonal
  exact Prime17Data.diagonalEval_eq_of_packed_checks Prime17Data.discriminant_check
    Prime17Data.invariant_check Prime17Data.invariant_nonnegative Prime17Data.trace_checks
    Prime17Data.elementary_zero_check Prime17Data.elementary_checks Prime17Data.diagonal_check

/-- Every actual singular modulus of discriminant `-68` has rational minimum support five. -/
theorem quartic68_singularModulus_minimumSupport {f : FormCoefficients}
    (hf : IsPrimitiveReducedForm 68 f) :
    let x := modularInvariant (quadraticPoint 68 f.a f.b)
    ∃ hx : IsIntegral ℚ x, minimumSupport hx = 5 := by
  apply quartic68_singularModulus_minimumSupport_of_integral hf
  intro n
  refine ⟨quartic68Int.coeff n, ?_⟩
  rw [analyticClassPolynomial_sixtyEight_eq_printed, Polynomial.coeff_map]
  rfl

end GRHArticle.SingularModuli
