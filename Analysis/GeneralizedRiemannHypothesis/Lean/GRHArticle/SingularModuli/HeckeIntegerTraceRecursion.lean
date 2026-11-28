import GRHArticle.SingularModuli.HeckeDiagonalTraceRecursion
import Mathlib.Data.Nat.Factorial.Basic

/-!
# An integer recurrence for the diagonal coefficient certificate

Multiplying the symmetric terms by their index factorial clears every
division in Newton's identities. Multiplying the final diagonal by
`p!` then leaves only integer series arithmetic.
-/

namespace GRHArticle.SingularModuli

open PowerSeries
open scoped PowerSeries
local notation "mapIntQ" => PowerSeries.map (Int.castRingHom ℚ)

/-- The elementary symmetric series scaled by its index factorial. -/
noncomputable def heckeScaledElementarySeries (p : ℕ) (F : ℤ⟦X⟧) : ℕ → ℤ⟦X⟧
  | 0 => 1
  | n + 1 => (-1) ^ (n + 2) *
    ∑ i : Fin (n + 1), (-1) ^ (i : ℕ) *
      C ((n.factorial / (i : ℕ).factorial : ℕ) : ℤ) * heckeScaledElementarySeries p F i *
      heckeTraceSeries p (n + 1 - i) F
termination_by n => n
decreasing_by exact i.isLt

private theorem C_factorial_ratio_mul {i n : ℕ} (hi : i ≤ n) :
    C ((n.factorial / i.factorial : ℕ) : ℚ) * C (i.factorial : ℚ) = C (n.factorial : ℚ) := by
  rw [← map_mul]
  exact congrArg C (by exact_mod_cast Nat.div_mul_cancel (Nat.factorial_dvd_factorial hi))

theorem map_heckeScaledElementarySeries (p : ℕ) (F : ℤ⟦X⟧) (n : ℕ) :
    mapIntQ (heckeScaledElementarySeries p F n) = C (n.factorial : ℚ) *
      heckeElementarySeries p F n := by
  induction n using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero =>
      simp [heckeScaledElementarySeries, heckeElementarySeries]
    | succ n =>
      have hh (i : Fin (n+1)) := ih i i.isLt
      have hs : C ((n+1).factorial : ℚ) * C ((↑(n+1) : ℚ)⁻¹) = C (n.factorial : ℚ) := by
        rw [← map_mul, Nat.factorial_succ, Nat.cast_mul]
        congr 1
        have hn : (↑(n+1) : ℚ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
        field_simp [hn]
      simp only [heckeScaledElementarySeries, heckeElementarySeries, map_mul, map_pow,
        map_neg, map_one, map_sum, map_C, Int.coe_castRingHom, Int.cast_natCast, hh]
      have hsum :
          (∑ i : Fin (n+1), (-1) ^ (i : ℕ) * C ((n.factorial / (i : ℕ).factorial : ℕ) : ℚ) *
            (C ((i : ℕ).factorial : ℚ) * heckeElementarySeries p F i) *
            mapIntQ (heckeTraceSeries p (n+1-i) F)) =
          C (n.factorial : ℚ) * ∑ i : Fin (n+1),
            (-1) ^ (i : ℕ) * heckeElementarySeries p F i *
              mapIntQ (heckeTraceSeries p (n+1-i) F) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ ↦ ?_
        have hi := C_factorial_ratio_mul (Nat.le_of_lt_succ i.isLt)
        calc
          _ = (C ((n.factorial / (i : ℕ).factorial : ℕ) : ℚ) * C ((i : ℕ).factorial : ℚ)) *
              ((-1) ^ (i : ℕ) * heckeElementarySeries p F i *
                mapIntQ (heckeTraceSeries p (n+1-i) F)) := by ring
          _ = _ := by rw [hi]
      rw [hsum]
      simp only [← mul_assoc, hs]
      ring

/-- The signed diagonal in the ordinary cusp variable scaled by `p!`. -/
noncomputable def heckeScaledDiagonalTraceSeries (p : ℕ+) (F : ℤ⟦X⟧) : ℤ⟦X⟧ :=
  let m : ℕ := p
  (expand m p.pos.ne' F - X ^ (m - 1) * F) *
    ∑ k ∈ Finset.range (m + 1), (-1) ^ k *
      C ((m.factorial / k.factorial : ℕ) : ℤ) * heckeScaledElementarySeries m F k * F ^ (m - k)

theorem map_heckeScaledDiagonalTraceSeries (p : ℕ+) (F : ℤ⟦X⟧) :
    mapIntQ (heckeScaledDiagonalTraceSeries p F) =
      C ((p : ℕ).factorial : ℚ) * heckeDiagonalTraceSeries p F := by
  simp only [heckeScaledDiagonalTraceSeries, heckeDiagonalTraceSeries, map_mul, map_pow, map_neg,
    map_one, map_sum, map_C, Int.coe_castRingHom, Int.cast_natCast, map_sub, map_expand,
    map_X, map_heckeScaledElementarySeries]
  have hsum :
      (∑ k ∈ Finset.range ((p : ℕ)+1), (-1)^k *
        C (((p : ℕ).factorial / k.factorial : ℕ) : ℚ) *
          (C (k.factorial : ℚ) * heckeElementarySeries (p : ℕ) F k) *
        (mapIntQ F)^((p : ℕ)-k)) =
      C ((p : ℕ).factorial : ℚ) * ∑ k ∈ Finset.range ((p : ℕ)+1),
        (-1)^k * heckeElementarySeries (p : ℕ) F k * (mapIntQ F)^((p : ℕ)-k) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    have hk' : k ≤ (p : ℕ) := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    calc
      _ = (C (((p : ℕ).factorial / k.factorial : ℕ) : ℚ) * C (k.factorial : ℚ)) *
          ((-1) ^ k * heckeElementarySeries (p : ℕ) F k * (mapIntQ F) ^ ((p : ℕ) - k)) := by ring
      _ = _ := by rw [C_factorial_ratio_mul hk']
  rw [hsum]
  ring

/-- Clearing the proposed polynomial in the ordinary variable uses only integer
operations. -/
noncomputable def clearedIntegerPolynomialEvaluation (P : Polynomial ℤ) (A : ℤ⟦X⟧) :
    ℕ → ℤ⟦X⟧
  | 0 => C (P.coeff 0)
  | n + 1 => X * clearedIntegerPolynomialEvaluation P A n +
      C (P.coeff (n + 1)) * A ^ (n + 1)

theorem map_clearedIntegerPolynomialEvaluation (P : Polynomial ℤ) (A : ℤ⟦X⟧) (n : ℕ) :
    mapIntQ (clearedIntegerPolynomialEvaluation P A n) =
      clearedRationalPolynomialEvaluation P (mapIntQ A) n := by
  induction n with
  | zero => simp [clearedIntegerPolynomialEvaluation, clearedRationalPolynomialEvaluation]
  | succ n ih => simp [clearedIntegerPolynomialEvaluation, clearedRationalPolynomialEvaluation, ih]

/-- A verification of `2*p+1` integer coefficient identities certifies the
proposed diagonal polynomial. -/
theorem primeHeckeDiagonalEval_eq_of_integerCertificate (p : ℕ+) [Fact (Nat.Prime (p : ℕ))]
    (P : Polynomial ℤ) (hP : P.natDegree ≤ 2 * (p : ℕ))
    (hcert : ∀ k ≤ 2 * (p : ℕ),
      (heckeScaledDiagonalTraceSeries p integralNormalizedJExpansion).coeff k =
        ((p : ℕ).factorial : ℤ) *
          (clearedIntegerPolynomialEvaluation P integralNormalizedJExpansion (2 * (p : ℕ))).coeff k) :
    ∀ z : UpperHalfPlane, Polynomial.aeval (modularInvariant z) P =
      -analyticPrimeHeckeDiagonal p z := by
  apply primeHeckeDiagonalEval_eq_of_rationalCertificate p P hP
  intro k hk
  have h₁ := congrArg (fun S : ℚ⟦X⟧ ↦ S.coeff k)
    (map_heckeScaledDiagonalTraceSeries p integralNormalizedJExpansion)
  have h₂ := congrArg (fun S : ℚ⟦X⟧ ↦ S.coeff k)
    (map_clearedIntegerPolynomialEvaluation P integralNormalizedJExpansion (2 * (p : ℕ)))
  simp only [coeff_map, coeff_C_mul, Int.coe_castRingHom] at h₁ h₂
  rw [hcert k hk, Int.cast_mul, Int.cast_natCast, h₂] at h₁
  symm
  exact mul_left_cancel₀ (by exact_mod_cast Nat.factorial_ne_zero (p : ℕ)) h₁

end GRHArticle.SingularModuli
