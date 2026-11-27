import GRHArticle.SingularModuli.QuarticAnalyticNumeric
import GRHArticle.SingularModuli.QuarticDiskCertificates

/-!
# Coefficient enclosures for the analytic quartic class polynomials
-/

namespace GRHArticle.SingularModuli

open Polynomial

private noncomputable def analyticQuartic (j : Fin 4 → ℂ) : ℂ[X] :=
  (X - C (j 0)) * ((X - C (j 1)) * ((X - C (j 2)) * (X - C (j 3))))

private theorem coeff_analyticQuartic (j : Fin 4 → ℂ) (n : Fin 5) :
    (analyticQuartic j).coeff n = quarticCoefficients (· + ·) (· * ·) Neg.neg 1 j n := by
  let s := j 0 + j 1
  let t := j 2 + j 3
  let p := j 0 * j 1
  let q := j 2 * j 3
  have hpoly : analyticQuartic j =
      C (p * q) + C (-(p * t + s * q)) * X + C (p + s * t + q) * X ^ 2 +
        C (-(s + t)) * X ^ 3 + X ^ 4 := by
    simp only [analyticQuartic, s, t, p, q, map_add, map_mul, map_neg]
    ring
  rw [hpoly]
  simp only [coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X_pow]
  fin_cases n <;> norm_num [quarticCoefficients, s, t, p, q]

private theorem quarticCoefficients_contains {A : Fin 4 → RationalComplexBox} {j : Fin 4 → ℂ}
    (hj : ∀ i, (A i).Contains (j i)) (n : Fin 5) :
    (quarticCoefficients RationalComplexBox.add RationalComplexBox.mul RationalComplexBox.neg
      (RationalComplexBox.point 1 0) A n).Contains ((analyticQuartic j).coeff n) := by
  rw [coeff_analyticQuartic]
  have hs := RationalComplexBox.contains_add (hj 0) (hj 1)
  have ht := RationalComplexBox.contains_add (hj 2) (hj 3)
  have hp := RationalComplexBox.contains_mul (hj 0) (hj 1)
  have hq := RationalComplexBox.contains_mul (hj 2) (hj 3)
  fin_cases n
  · exact RationalComplexBox.contains_mul hp hq
  · exact RationalComplexBox.contains_neg
      (RationalComplexBox.contains_add (RationalComplexBox.contains_mul hp ht)
        (RationalComplexBox.contains_mul hs hq))
  · exact RationalComplexBox.contains_add
      (RationalComplexBox.contains_add hp (RationalComplexBox.contains_mul hs ht)) hq
  · exact RationalComplexBox.contains_neg (RationalComplexBox.contains_add hs ht)
  · simp [quarticCoefficients, RationalComplexBox.Contains, RationalComplexBox.point,
      RationalInterval.Contains, RationalInterval.point]

private noncomputable def actualRoot55 (i : Fin 4) : ℂ :=
  modularInvariant (quadraticPoint 55 (quartic55Form i).a (quartic55Form i).b)

private noncomputable def actualRoot68 (i : Fin 4) : ℂ :=
  modularInvariant (quadraticPoint 68 (quartic68Form i).a (quartic68Form i).b)

private theorem actualRoot55_class : analyticClassPolynomial 55 = analyticQuartic actualRoot55 := by
  rw [analyticClassPolynomial, reducedForms_fiftyFive]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  rfl

private theorem actualRoot68_class : analyticClassPolynomial 68 = analyticQuartic actualRoot68 := by
  rw [analyticClassPolynomial, reducedForms_sixtyEight]
  rw [Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  rfl

theorem quartic55AnalyticCoefficientBox_contains (n : Fin 5) :
    (quartic55AnalyticCoefficientBox n).Contains ((analyticClassPolynomial 55).coeff n) := by
  rw [actualRoot55_class]
  exact quarticCoefficients_contains quartic55_modularInvariant_box_contains n

theorem quartic68AnalyticCoefficientBox_contains (n : Fin 5) :
    (quartic68AnalyticCoefficientBox n).Contains ((analyticClassPolynomial 68).coeff n) := by
  rw [actualRoot68_class]
  exact quarticCoefficients_contains quartic68_modularInvariant_box_contains n

private theorem eq_of_contains_of_isolates {A : RationalInterval} {k v : ℤ}
    (hc : A.Contains (v : ℝ)) (hi : A.IsolatesInteger k) : v = k := by
  have hlo := (Rat.cast_lt (K := ℝ)).mpr hi.1
  have hhi := (Rat.cast_lt (K := ℝ)).mpr hi.2
  push_cast at hlo hhi
  have hl : k - 1 < v := by
    have h : ((k : ℝ) - 1) < (v : ℝ) := by linarith only [hlo, hc.1]
    exact_mod_cast h
  have hu : v < k + 1 := by
    have h : (v : ℝ) < (k : ℝ) + 1 := by linarith only [hhi, hc.2]
    exact_mod_cast h
  omega

private theorem polynomial_eq_of_box_rounding {P : ℂ[X]} {Q : ℤ[X]} (hP : P.natDegree = 4)
    (hQ : Q.natDegree = 4) {A : Fin 5 → RationalComplexBox}
    (hbox : ∀ n : Fin 5, (A n).Contains (P.coeff n))
    (hiso : ∀ n : Fin 5, (A n).re.IsolatesInteger (Q.coeff n))
    (hint : ∀ n : Fin 5, ∃ k : ℤ, P.coeff n = (k : ℂ)) :
    P = Q.map (Int.castRingHom ℂ) := by
  ext n
  by_cases hn : n < 5
  · let i : Fin 5 := ⟨n, hn⟩
    obtain ⟨v, hv⟩ := hint i
    have hc := (hbox i).1
    rw [hv, Complex.intCast_re] at hc
    have he := eq_of_contains_of_isolates hc (hiso i)
    rw [Polynomial.coeff_map]
    exact hv.trans (congrArg (fun k : ℤ ↦ (k : ℂ)) he)
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hP]; omega),
      Polynomial.coeff_map, Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hQ]; omega), map_zero]

/-- The coefficient table in the numerical certificate is the printed quartic. -/
theorem quartic55_printed_coeff (n : Fin 5) :
    quartic55Int.coeff n = quartic55PrintedCoefficient n := by
  simp only [quartic55Int, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X_pow]
  fin_cases n <;> norm_num [quartic55PrintedCoefficient]

theorem quartic68_printed_coeff (n : Fin 5) :
    quartic68Int.coeff n = quartic68PrintedCoefficient n := by
  simp only [quartic68Int, coeff_add, coeff_C, coeff_C_mul_X, coeff_C_mul_X_pow, coeff_X_pow]
  fin_cases n <;> norm_num [quartic68PrintedCoefficient]

theorem abs_sub_lt_half_of_box {A : RationalInterval} {x : ℝ} {k : ℤ}
    (hc : A.Contains x) (hi : A.IsolatesInteger k) : |x - (k : ℝ)| < 1 / 2 := by
  have hl := (Rat.cast_lt (K := ℝ)).mpr hi.1
  have hu := (Rat.cast_lt (K := ℝ)).mpr hi.2
  push_cast at hl hu
  exact abs_lt.mpr ⟨by linarith only [hl, hc.1], by linarith only [hu, hc.2]⟩

/-- Rounding the certified coefficient boxes identifies the printed -55 quartic
when the boxes isolate its coefficients and the analytic coefficients are integers. -/
theorem analyticClassPolynomial_fiftyFive_eq_printed_of_certificate
    (hiso : ∀ n : Fin 5, (quartic55AnalyticCoefficientBox n).re.IsolatesInteger
      (quartic55PrintedCoefficient n))
    (hint : ∀ n : Fin 5, ∃ k : ℤ, (analyticClassPolynomial 55).coeff n = (k : ℂ)) :
    analyticClassPolynomial 55 = quartic55Int.map (Int.castRingHom ℂ) :=
  polynomial_eq_of_box_rounding analyticClassPolynomial_fiftyFive_natDegree quartic55Int_natDegree
    quartic55AnalyticCoefficientBox_contains (fun n ↦ by rw [quartic55_printed_coeff]; exact hiso n) hint

/-- Rounding the certified coefficient boxes identifies the printed -68 quartic
when the boxes isolate its coefficients and the analytic coefficients are integers. -/
theorem analyticClassPolynomial_sixtyEight_eq_printed_of_certificate
    (hiso : ∀ n : Fin 5, (quartic68AnalyticCoefficientBox n).re.IsolatesInteger
      (quartic68PrintedCoefficient n))
    (hint : ∀ n : Fin 5, ∃ k : ℤ, (analyticClassPolynomial 68).coeff n = (k : ℂ)) :
    analyticClassPolynomial 68 = quartic68Int.map (Int.castRingHom ℂ) :=
  polynomial_eq_of_box_rounding analyticClassPolynomial_sixtyEight_natDegree quartic68Int_natDegree
    quartic68AnalyticCoefficientBox_contains (fun n ↦ by rw [quartic68_printed_coeff]; exact hiso n) hint

end GRHArticle.SingularModuli
