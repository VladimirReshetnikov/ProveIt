import GRHArticle.SingularModuli.QuarticAnalyticEnclosure
import GRHArticle.SingularModuli.QuarticCoefficientChecks
import GRHArticle.SingularModuli.QuarticSupport

/-!
# The analytic class-polynomial certificates at discriminants -55 and -68

The complex interval calculations leave the integrality of the analytic
class-polynomial coefficients as the algebraic input to exact identification.
-/

namespace GRHArticle.SingularModuli

open Polynomial

private theorem eval_integer_polynomial_as_rat (P : ℤ[X]) (z : ℂ) :
    aeval z (P.map (Int.castRingHom ℚ)) = (P.map (Int.castRingHom ℂ)).eval z := by
  have hmap : (algebraMap ℚ ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ := by
    ext a
    simp
  rw [Polynomial.aeval_def, Polynomial.eval₂_map, hmap, Polynomial.eval_map]

/-- The real analytic coefficients at discriminant -55 are within half a unit
of the printed integers. -/
theorem analyticClassPolynomial_fiftyFive_realCoefficient_enclosure (n : Fin 5) :
    |((analyticClassPolynomial 55).coeff n).re - (↑(quartic55Int.coeff n) : ℝ)| < 1 / 2 := by
  rw [quartic55_printed_coeff]
  exact abs_sub_lt_half_of_box (quartic55AnalyticCoefficientBox_contains n).1
    (quartic55_analyticCoefficient_isolates n)

/-- Integrality identifies the analytic polynomial at discriminant -55 with the
printed quartic whose coefficients lie in the verified enclosures. -/
theorem analyticClassPolynomial_fiftyFive_eq_printed_of_integral
    (hint : ∀ n : Fin 5, ∃ k : ℤ, (analyticClassPolynomial 55).coeff n = (k : ℂ)) :
    analyticClassPolynomial 55 = quartic55Int.map (Int.castRingHom ℂ) :=
  analyticClassPolynomial_fiftyFive_eq_printed_of_certificate quartic55_analyticCoefficient_isolates hint

/-- Integrality of the analytic class-polynomial coefficients suffices to apply
the checked p-adic certificate to the actual singular modulus of every reduced form. -/
theorem quartic55_singularModulus_minimumSupport_of_integral {f : FormCoefficients}
    (hf : IsPrimitiveReducedForm 55 f)
    (hint : ∀ n : Fin 5, ∃ k : ℤ, (analyticClassPolynomial 55).coeff n = (k : ℂ)) :
    let x := modularInvariant (quadraticPoint 55 f.a f.b)
    ∃ hx : IsIntegral ℚ x, minimumSupport hx = 5 := by
  let x := modularInvariant (quadraticPoint 55 f.a f.b)
  have hz : (analyticClassPolynomial 55).eval x = 0 :=
    (analyticClassPolynomial_eval_eq_zero_iff 55 x).2 ⟨f, hf, rfl⟩
  rw [analyticClassPolynomial_fiftyFive_eq_printed_of_integral hint] at hz
  have hx : aeval x quartic55 = 0 := by
    unfold quartic55
    rwa [eval_integer_polynomial_as_rat]
  exact ⟨⟨quartic55, quartic55_monic, hx⟩, quartic55_minimumSupport x hx⟩

/-- The real analytic coefficients at discriminant -68 are within half a unit
of the printed integers. -/
theorem analyticClassPolynomial_sixtyEight_realCoefficient_enclosure (n : Fin 5) :
    |((analyticClassPolynomial 68).coeff n).re - (↑(quartic68Int.coeff n) : ℝ)| < 1 / 2 := by
  rw [quartic68_printed_coeff]
  exact abs_sub_lt_half_of_box (quartic68AnalyticCoefficientBox_contains n).1
    (quartic68_analyticCoefficient_isolates n)

/-- Integrality identifies the analytic polynomial at discriminant -68 with the
printed quartic whose coefficients lie in the verified enclosures. -/
theorem analyticClassPolynomial_sixtyEight_eq_printed_of_integral
    (hint : ∀ n : Fin 5, ∃ k : ℤ, (analyticClassPolynomial 68).coeff n = (k : ℂ)) :
    analyticClassPolynomial 68 = quartic68Int.map (Int.castRingHom ℂ) :=
  analyticClassPolynomial_sixtyEight_eq_printed_of_certificate quartic68_analyticCoefficient_isolates hint

/-- Integrality of the analytic class-polynomial coefficients suffices to apply
the checked p-adic certificate to the actual singular modulus of every reduced form. -/
theorem quartic68_singularModulus_minimumSupport_of_integral {f : FormCoefficients}
    (hf : IsPrimitiveReducedForm 68 f)
    (hint : ∀ n : Fin 5, ∃ k : ℤ, (analyticClassPolynomial 68).coeff n = (k : ℂ)) :
    let x := modularInvariant (quadraticPoint 68 f.a f.b)
    ∃ hx : IsIntegral ℚ x, minimumSupport hx = 5 := by
  let x := modularInvariant (quadraticPoint 68 f.a f.b)
  have hz : (analyticClassPolynomial 68).eval x = 0 :=
    (analyticClassPolynomial_eval_eq_zero_iff 68 x).2 ⟨f, hf, rfl⟩
  rw [analyticClassPolynomial_sixtyEight_eq_printed_of_integral hint] at hz
  have hx : aeval x quartic68 = 0 := by
    unfold quartic68
    rwa [eval_integer_polynomial_as_rat]
  exact ⟨⟨quartic68, quartic68_monic, hx⟩, quartic68_minimumSupport x hx⟩

end GRHArticle.SingularModuli
