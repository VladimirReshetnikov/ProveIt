import GRHArticle.SingularModuli.CMHeckeIntegralDiagonal

/-!
# Finite coefficient equality for cleared polynomial evaluations

After substituting a series with constant coefficient one, the coefficient
at each of `0,s,2*s,...,n*s` determines the next polynomial coefficient.
This gives a finite certificate for the polynomial defining a Hecke diagonal.
-/

namespace GRHArticle.SingularModuli

open Polynomial PowerSeries
open scoped PowerSeries

private theorem constantCoeff_clearedSeriesEvaluation (P : Polynomial ℂ) {s : ℕ}
    (hs : s ≠ 0) {A : ℂ⟦X⟧} (hA : A.constantCoeff = 1) (n : ℕ) :
    (clearedSeriesPolynomialEvaluation P s A n).constantCoeff = P.coeff n := by
  cases n <;> simp [clearedSeriesPolynomialEvaluation, zero_pow hs, hA]

private theorem coeff_eq_of_clearedSeriesEvaluation_prefix (P Q : Polynomial ℂ) {s : ℕ}
    (hs : s ≠ 0) {A : ℂ⟦X⟧} (hA : A.constantCoeff = 1) (n : ℕ)
    (h : ∀ k ≤ n,
      (clearedSeriesPolynomialEvaluation P s A n).coeff (s*k) =
        (clearedSeriesPolynomialEvaluation Q s A n).coeff (s*k)) :
    ∀ i ≤ n, P.coeff i = Q.coeff i := by
  have htop (m : ℕ)
      (he : (clearedSeriesPolynomialEvaluation P s A m).coeff (s*0) =
        (clearedSeriesPolynomialEvaluation Q s A m).coeff (s*0)) :
      P.coeff m = Q.coeff m := by
    simpa only [Nat.mul_zero, coeff_zero_eq_constantCoeff_apply,
      constantCoeff_clearedSeriesEvaluation P hs hA, constantCoeff_clearedSeriesEvaluation Q hs hA]
      using he
  induction n with
  | zero =>
    intro i hi
    rw [Nat.eq_zero_of_le_zero hi]
    exact htop _ (h 0 le_rfl)
  | succ n ih =>
    have hPQ := htop _ (h 0 (Nat.zero_le _))
    have htail (k : ℕ) (hk : k ≤ n) :
        (clearedSeriesPolynomialEvaluation P s A n).coeff (s*k) =
          (clearedSeriesPolynomialEvaluation Q s A n).coeff (s*k) := by
      have hstep := h (k + 1) (Nat.succ_le_succ hk)
      simpa only [Nat.mul_succ, clearedSeriesPolynomialEvaluation, map_add, PowerSeries.coeff_X_pow_mul,
        hPQ, add_left_inj] using hstep
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | rfl
    · exact ih htail i (Nat.lt_succ_iff.mp hlt)
    · exact hPQ

/-- Degree-`n` polynomials agree if these `n+1` coefficients agree after
clearing the same substitution with a series of constant coefficient one. -/
theorem eq_of_clearedSeriesPolynomialEvaluation_prefix (P Q : Polynomial ℂ) {s : ℕ}
    (hs : s ≠ 0) {A : ℂ⟦X⟧} (hA : A.constantCoeff = 1) (n : ℕ)
    (hP : P.natDegree ≤ n) (hQ : Q.natDegree ≤ n)
    (h : ∀ k ≤ n,
      (clearedSeriesPolynomialEvaluation P s A n).coeff (s*k) =
        (clearedSeriesPolynomialEvaluation Q s A n).coeff (s*k)) : P = Q := by
  ext i
  rcases le_or_gt i n with hi | hi
  · exact coeff_eq_of_clearedSeriesEvaluation_prefix P Q hs hA n h i hi
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt hi),
      Polynomial.coeff_eq_zero_of_natDegree_lt (hQ.trans_lt hi)]

/-- A proposed integer diagonal polynomial can be verified by comparing
`2*p+1` coefficients in the cleared series. -/
theorem primeHeckeDiagonalEval_eq_of_finiteCertificate (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (P : Polynomial ℤ) (hP : P.natDegree ≤ 2 * (p : ℕ))
    (hcert : ∀ k ≤ 2 * (p : ℕ),
      (primeHeckeDiagonalSeries p).coeff ((p : ℕ) * k) =
        (clearedSeriesPolynomialEvaluation (P.map (Int.castRingHom ℂ)) (p : ℕ)
          (expand (p : ℕ) p.pos.ne'
            (PowerSeries.map (Int.castRingHom ℂ) integralNormalizedJExpansion))
          (2 * (p : ℕ))).coeff ((p : ℕ) * k)) :
    ∀ z : UpperHalfPlane, aeval (modularInvariant z) P = -analyticPrimeHeckeDiagonal p z := by
  obtain ⟨Q, hQmonic, hQdeg, hQ⟩ := exists_monic_poly_analyticPrimeHeckeDiagonal p
  let A := expand (p : ℕ) p.pos.ne'
    (PowerSeries.map (Int.castRingHom ℂ) integralNormalizedJExpansion)
  have hA : A.constantCoeff = 1 := by
    change (expand (p : ℕ) p.pos.ne'
      (PowerSeries.map (Int.castRingHom ℂ) integralNormalizedJExpansion)).constantCoeff = 1
    rw [constantCoeff_expand, ← coeff_zero_eq_constantCoeff_apply, PowerSeries.coeff_map,
      coeff_zero_eq_constantCoeff_apply, constantCoeff_integralNormalizedJExpansion, map_one]
  have hP' : (P.map (Int.castRingHom ℂ)).natDegree ≤ 2 * (p : ℕ) := by
    rw [Polynomial.natDegree_map_eq_of_injective Int.cast_injective]
    exact hP
  have he := eq_of_clearedSeriesPolynomialEvaluation_prefix (P.map (Int.castRingHom ℂ)) Q
    p.pos.ne' hA (2 * (p : ℕ)) hP' hQdeg.le fun k hk ↦ by
      rw [← primeHeckeDiagonalSeries_eq_clearedSeriesPolynomialEvaluation p Q hQmonic hQdeg hQ]
      exact (hcert k hk).symm
  intro z
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, algebraMap_int_eq, he, hQ]

/-- The certified integer diagonal factors give a root of the selected
factor when the residual factor is nonzero at the CM value. -/
theorem aeval_factor_eq_zero_of_primeHeckeDiagonal_zero (p : ℕ+)
    (P H R : Polynomial ℤ) (e : ℕ) {z : UpperHalfPlane}
    (hP : aeval (modularInvariant z) P = -analyticPrimeHeckeDiagonal p z)
    (hfactor : P = H ^ e * R) (hzero : analyticPrimeHeckeDiagonal p z = 0)
    (hR : aeval (modularInvariant z) R ≠ 0) :
    aeval (modularInvariant z) H = 0 := by
  rw [hzero, neg_zero, hfactor, map_mul, map_pow] at hP
  exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hP).resolve_right hR)

end GRHArticle.SingularModuli
