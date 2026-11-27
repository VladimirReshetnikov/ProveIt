import GRHArticle.SingularModuli.EisensteinTruncation
import GRHArticle.SingularModuli.EtaTruncation
import GRHArticle.SingularModuli.ReducedForms

/-!
# Truncation errors at quadratic points

The two error bounds apply simultaneously to the actual value used for
each factor of the analytic class polynomial. The eta bound precedes the
twenty-fourth power in the verifier's denominator.
-/

namespace GRHArticle.SingularModuli

/-- The numerator series and the unpowered denominator product in the
integer class-polynomial verifier, evaluated at any enumerated form. -/
theorem classPolynomial_truncation_bounds (D : ℕ+) (f : FormCoefficients) (hf : f ∈ reducedForms D) :
    let z := quadraticPoint D f.a f.b
    let q := Function.Periodic.qParam 1 z
    ‖ModularForm.E₄ z - (1 + 240 * ∑ n ∈ Finset.range 164,
      (ArithmeticFunction.sigma 3 (n + 1) : ℂ) * q ^ (n + 1))‖ ≤ 960 * 165 ^ 3 / 200 ^ 165 ∧
    ‖(∏' n : ℕ, (1 - q ^ (n + 1))) - (∏ n ∈ Finset.range 164, (1 - q ^ (n + 1)))‖ <
      8 / 200 ^ 165 := by
  intro z q
  have h := (mem_reducedForms_iff D f).1 hf
  have hq : ‖q‖ ≤ 1 / 200 := (norm_qParam_quadraticPoint_lt D f.a f.b
    (three_mul_sq_le_of_reduced D f.a f.b f.c h.1 h.2.1 h.2.2.1)).le
  exact ⟨by simpa only [eisensteinFour_qExpansion] using norm_eisensteinFour_sub_trunc164_le q hq,
    norm_eulerProduct_sub_trunc164_lt hq⟩

end GRHArticle.SingularModuli
