import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.Polynomial.Eval.Subring
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Recovering integer polynomial coefficients from a cleared series

If a series `J` starts with `1`, the constant coefficient of the cleared
evaluation of `P(J / X^s)` is the highest relevant coefficient of `P`.
Subtracting that term and shifting down by `s` extracts the other coefficients.
-/

namespace GRHArticle.SingularModuli

open scoped PowerSeries
open PowerSeries

local notation "intSeriesMap" => PowerSeries.map (Int.castRingHom ℂ)

/-- Replace `P(Y)` by the polynomial terms of degree at most `n), evaluated
at `J / X^s` and multiplied by `X^(s*n)`. -/
noncomputable def clearedSeriesPolynomialEvaluation (P : Polynomial ℂ)
    (s : ℕ) (J : ℂ⟦X⟧) : ℕ → ℂ⟦X⟧
  | 0 => C (P.coeff 0)
  | n + 1 => X ^ s * clearedSeriesPolynomialEvaluation P s J n + C (P.coeff (n + 1)) * J ^ (n + 1)

private theorem constantCoeff_clearedSeriesPolynomialEvaluation (P : Polynomial ℂ)
    {s : ℕ} (hs : s ≠ 0) (J : ℂ⟦X⟧) (hJ : constantCoeff J = 1) (n : ℕ) :
    constantCoeff (clearedSeriesPolynomialEvaluation P s J n) = P.coeff n := by
  cases n <;> simp [clearedSeriesPolynomialEvaluation, zero_pow hs, hJ]

private theorem exists_int_of_coeff_clearedSeriesPolynomialEvaluation (P : Polynomial ℂ)
    {s : ℕ} (hs : s ≠ 0) (J : ℤ⟦X⟧) (hJ : constantCoeff J = 1)
    (n : ℕ) (F : ℤ⟦X⟧)
    (hF : intSeriesMap F = clearedSeriesPolynomialEvaluation P s (intSeriesMap J) n) :
    ∀ i ≤ n, ∃ c : ℤ, P.coeff i = (c : ℂ) := by
  have hJ' : constantCoeff (intSeriesMap J) = 1 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply, hJ]
    norm_num
  have htop (m : ℕ) (G : ℤ⟦X⟧)
      (hG : intSeriesMap G = clearedSeriesPolynomialEvaluation P s (intSeriesMap J) m) :
      P.coeff m = (constantCoeff (R := ℤ) G : ℂ) := by
    have h := congrArg (constantCoeff (R := ℂ)) hG
    rw [constantCoeff_clearedSeriesPolynomialEvaluation P hs _ hJ'] at h
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_map, coeff_zero_eq_constantCoeff_apply] at h
    exact h.symm
  induction n generalizing F with
  | zero =>
    intro i hi
    rw [Nat.eq_zero_of_le_zero hi]
    exact ⟨constantCoeff F, htop _ F hF⟩
  | succ n ih =>
    intro i hi
    rcases lt_or_eq_of_le hi with hlt | heq
    · let W := F - C (constantCoeff F) * J ^ (n + 1)
      have hW : intSeriesMap W = X ^ s * clearedSeriesPolynomialEvaluation P s (intSeriesMap J) n := by
        simp only [W, map_sub, map_mul, map_pow, map_C, Int.coe_castRingHom, hF,
          clearedSeriesPolynomialEvaluation, htop _ F hF, add_sub_cancel_right]
      let G : ℤ⟦X⟧ := PowerSeries.mk fun j ↦ W.coeff (j + s)
      have hG : intSeriesMap G = clearedSeriesPolynomialEvaluation P s (intSeriesMap J) n := by
        ext j
        calc
          (intSeriesMap G).coeff j = (intSeriesMap W).coeff (j + s) := by
            rw [coeff_map, coeff_map]
            change (Int.castRingHom ℂ) (coeff j (PowerSeries.mk fun k ↦ W.coeff (k + s))) =
              (Int.castRingHom ℂ) (W.coeff (j + s))
            rw [coeff_mk]
          _ = (clearedSeriesPolynomialEvaluation P s (intSeriesMap J) n).coeff j := by
            rw [hW, coeff_X_pow_mul]
      exact ih G hG i (Nat.lt_succ_iff.mp hlt)
    · subst i
      exact ⟨constantCoeff F, htop _ F hF⟩

/-- An integral normalized series with constant coefficient `1` reveals
integer polynomial coefficients after clearing the powers of `X`. -/
theorem exists_intPolynomial_of_clearedSeriesPolynomialEvaluation (P : Polynomial ℂ)
    {s : ℕ} (hs : s ≠ 0) (J : ℤ⟦X⟧) (hJ : constantCoeff J = 1)
    (n : ℕ) (hn : P.natDegree ≤ n) (F : ℤ⟦X⟧)
    (hF : intSeriesMap F = clearedSeriesPolynomialEvaluation P s (intSeriesMap J) n) :
    ∃ Q : Polynomial ℤ, Q.map (Int.castRingHom ℂ) = P := by
  apply (Polynomial.mem_map_range (Int.castRingHom ℂ)).2
  intro i
  rcases le_or_gt i n with hi | hi
  · obtain ⟨z, hz⟩ := exists_int_of_coeff_clearedSeriesPolynomialEvaluation P hs J hJ n F hF i hi
    exact ⟨z, hz.symm⟩
  · exact ⟨0, by simp [Polynomial.coeff_eq_zero_of_natDegree_lt (hn.trans_lt hi)]⟩

end GRHArticle.SingularModuli
