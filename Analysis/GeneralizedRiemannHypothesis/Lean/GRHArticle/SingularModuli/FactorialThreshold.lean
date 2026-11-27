import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Factorial valuation bounds for sparse polynomials

This file formalizes the arithmetic of the depth thresholds in Article section
`smd:cor:threshold`. The weight comparisons are over rational depths and are
independent of the analytic root-count argument.
-/

namespace GRHArticle.SingularModuli

/-- The valuation of the product of the integers from `i + 1` through `i + d`. -/
def factorialIntervalValuation (p i d : ℕ) : ℕ :=
  padicValNat p ((i + d).factorial / i.factorial)

private theorem factorialIntervalValuation_le_factorial (p i d : ℕ) [Fact p.Prime] :
    factorialIntervalValuation p i d ≤ padicValNat p (i + d).factorial := by
  rw [factorialIntervalValuation,
    padicValNat.div_of_dvd (Nat.factorial_dvd_factorial (Nat.le_add_right i d))]
  exact Nat.sub_le _ _

private theorem factorialValuation_eq_zero_of_lt {p n : ℕ} [hp : Fact p.Prime] (h : n < p) :
    padicValNat p n.factorial = 0 :=
  padicValNat.eq_zero_of_not_dvd fun hdiv => (not_le_of_gt h) (hp.out.dvd_factorial.mp hdiv)

/-- The factorial interval bound in the depth-threshold criterion for `p ≥ t`. -/
theorem factorialIntervalValuation_mul_le {p t i d : ℕ} [hp : Fact p.Prime]
    (ht : 2 ≤ t) (htp : t ≤ p) (hi : i < t) (hd : 0 < d) :
    (p - t + 1) * factorialIntervalValuation p i d ≤ d := by
  let v := factorialIntervalValuation p i d
  have hp₁ : 0 < p - 1 := by omega
  have hval : (p - 1) * v < i + d :=
    lt_of_le_of_lt
      (Nat.mul_le_mul_left (p - 1) (factorialIntervalValuation_le_factorial p i d))
      (sub_one_mul_padicValNat_factorial_lt_of_ne_zero p (by omega))
  change (p - t + 1) * v ≤ d
  by_cases hi₀ : i = 0
  · have hcoef : p - t + 1 ≤ p - 1 := by omega
    exact (Nat.mul_le_mul_right v hcoef).trans (by omega)
  by_cases hsmall : i + d < p
  · have hv : v = 0 := Nat.eq_zero_of_le_zero
      ((factorialIntervalValuation_le_factorial p i d).trans_eq
        (factorialValuation_eq_zero_of_lt hsmall))
    simp [hv]
  have hfirst : p - i ≤ d := by omega
  have hsplit : (p - i) + (i - 1) = p - 1 := by omega
  have htotal : i + d - 1 = d + (i - 1) := by omega
  have hcross : (p - i) * (i + d - 1) ≤ d * (p - 1) := by
    rw [htotal, ← hsplit, Nat.mul_add, Nat.mul_add, Nat.mul_comm (p - i) d]
    exact Nat.add_le_add_left (Nat.mul_le_mul_right (i - 1) hfirst) _
  have hstrong : (p - i) * v ≤ d := by
    apply Nat.le_of_mul_le_mul_left _ hp₁
    calc
      (p - 1) * ((p - i) * v) = (p - i) * ((p - 1) * v) := Nat.mul_left_comm _ _ _
      _ ≤ (p - i) * (i + d - 1) := Nat.mul_le_mul_left _ (by omega)
      _ ≤ d * (p - 1) := hcross
      _ = (p - 1) * d := Nat.mul_comm _ _
  exact (Nat.mul_le_mul_right v (by omega)).trans hstrong

private theorem padicValNat_le_of_not_dvd_succ {p m k : ℕ} (h : ¬p ^ (k + 1) ∣ m) :
    padicValNat p m ≤ k :=
  le_of_not_gt fun hk => h ((pow_dvd_pow p hk).trans pow_padicValNat_dvd)

/-- The small-prime factorial interval bound at `p = 2` and `t ≤ 5`. -/
theorem factorialIntervalValuation_two_le {i d : ℕ} (hi : i < 5) (hd : 0 < d) :
    factorialIntervalValuation 2 i d ≤ 2 * d := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_cases h : 3 ≤ d
  · have hv : (2 - 1) * factorialIntervalValuation 2 i d < i + d :=
      lt_of_le_of_lt
        (Nat.mul_le_mul_left _ (factorialIntervalValuation_le_factorial 2 i d))
        (sub_one_mul_padicValNat_factorial_lt_of_ne_zero 2 (by omega))
    omega
  interval_cases i <;> interval_cases d <;>
    exact padicValNat_le_of_not_dvd_succ (by decide)

/-- The small-prime factorial interval bound at `p = 3` and `t ≤ 5`. -/
theorem factorialIntervalValuation_three_le {i d : ℕ} (hi : i < 5) (hd : 0 < d) :
    factorialIntervalValuation 3 i d ≤ d := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  by_cases h : 3 ≤ d
  · have hv : (3 - 1) * factorialIntervalValuation 3 i d < i + d :=
      lt_of_le_of_lt
        (Nat.mul_le_mul_left _ (factorialIntervalValuation_le_factorial 3 i d))
        (sub_one_mul_padicValNat_factorial_lt_of_ne_zero 3 (by omega))
    omega
  interval_cases i <;> interval_cases d <;>
    exact padicValNat_le_of_not_dvd_succ (by decide)

/-- The weight `w_{p,r}(n)` of the factorial denominator and the depth factor. -/
def factorialWeight (p : ℕ) (r : ℚ) (n : ℕ) : ℚ :=
  r * n - padicValNat p n.factorial

private theorem factorialValuation_add {p i d : ℕ} [Fact p.Prime] :
    padicValNat p (i + d).factorial =
      factorialIntervalValuation p i d + padicValNat p i.factorial := by
  have hprod : (i + d).factorial / i.factorial * i.factorial = (i + d).factorial :=
    Nat.div_mul_cancel (Nat.factorial_dvd_factorial (Nat.le_add_right i d))
  have hquot : (i + d).factorial / i.factorial ≠ 0 := by
    intro hz
    exact Nat.factorial_ne_zero (i + d) (by simpa [hz] using hprod.symm)
  rw [factorialIntervalValuation, ← padicValNat.mul hquot (Nat.factorial_ne_zero i), hprod]

/-- Any admissible factorial interval bound gives a strict weight gap at greater depth. -/
theorem factorialWeight_lt_add_of_bound {p i d : ℕ} [Fact p.Prime] {κ r : ℚ}
    (hval : (factorialIntervalValuation p i d : ℚ) ≤ (d : ℚ) * κ)
    (hr : κ < r) (hd : 0 < d) :
    factorialWeight p r i < factorialWeight p r (i + d) := by
  have hprod := mul_lt_mul_of_pos_left hr (Nat.cast_pos.mpr hd : (0 : ℚ) < d)
  simp only [factorialWeight, factorialValuation_add, Nat.cast_add, mul_add]
  linarith only [hval, hprod, mul_comm r (d : ℚ)]

/-- Strict weight comparison for `p ≥ t` and the article's depth `1/(p-t+1)`. -/
theorem factorialWeight_lt_add_of_prime_ge_terms {p t i d : ℕ} [Fact p.Prime] {r : ℚ}
    (ht : 2 ≤ t) (htp : t ≤ p) (hi : i < t) (hd : 0 < d)
    (hr : 1 / ((p - t + 1 : ℕ) : ℚ) < r) :
    factorialWeight p r i < factorialWeight p r (i + d) := by
  refine factorialWeight_lt_add_of_bound ?_ hr hd
  have hden : (0 : ℚ) < ((p - t + 1 : ℕ) : ℚ) := Nat.cast_pos.mpr (by omega)
  rw [one_div, ← div_eq_mul_inv, le_div_iff₀ hden, mul_comm]
  exact_mod_cast factorialIntervalValuation_mul_le ht htp hi hd

/-- Strict weight comparison at `p = 2` and depth greater than two. -/
theorem factorialWeight_two_lt_add {i d : ℕ} {r : ℚ}
    (hi : i < 5) (hd : 0 < d) (hr : 2 < r) :
    factorialWeight 2 r i < factorialWeight 2 r (i + d) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  refine factorialWeight_lt_add_of_bound ?_ hr hd
  rw [mul_comm]
  exact_mod_cast factorialIntervalValuation_two_le hi hd

/-- Strict weight comparison at `p = 3` and depth greater than one. -/
theorem factorialWeight_three_lt_add {i d : ℕ} {r : ℚ}
    (hi : i < 5) (hd : 0 < d) (hr : 1 < r) :
    factorialWeight 3 r i < factorialWeight 3 r (i + d) := by
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  refine factorialWeight_lt_add_of_bound ?_ hr hd
  rw [mul_one]
  exact_mod_cast factorialIntervalValuation_three_le hi hd

end GRHArticle.SingularModuli
