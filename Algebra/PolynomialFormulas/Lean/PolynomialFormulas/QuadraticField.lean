import PolynomialFormulas.Basic

/-!
# The quadratic formula with its exact characteristic hypothesis

`Basic.lean` supplies the characteristic-zero API used by the low-degree
solvers.  Lazard's displayed quadratic step has the sharper scope
`2 ≠ 0`.  This file records that exact field-generic statement without
changing the existing API: a square root is still supplied by its defining
equation, and the two displayed values are proved sound and exhaustive.
-/

namespace LeanProofs.PolynomialFormulas

section Field

variable {K : Type*} [Field K]

/-- The `+` branch needs only that its displayed denominator is nonzero. -/
theorem quadratic_formula_plus_of_two_ne_zero {a b c s : K}
    (h2 : (2 : K) ≠ 0) (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
    quadratic a b c ((-b + s) / (2 * a)) = 0 := by
  unfold quadratic
  field_simp [h2, ha]
  linear_combination hs

/-- The `-` branch under the exact same denominator hypothesis. -/
theorem quadratic_formula_minus_of_two_ne_zero {a b c s : K}
    (h2 : (2 : K) ≠ 0) (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
    quadratic a b c ((-b - s) / (2 * a)) = 0 := by
  simpa [sub_eq_add_neg] using
    (quadratic_formula_plus_of_two_ne_zero
      (s := -s) h2 ha (by simpa using hs))

/-- Every entry of the existing two-value solver is a root when `2 ≠ 0`. -/
theorem solveQuadratic_correct_of_two_ne_zero {a b c s : K}
    (h2 : (2 : K) ≠ 0) (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) (i : Fin 2) :
    quadratic a b c (solveQuadratic a b c s i) = 0 := by
  fin_cases i
  · exact quadratic_formula_plus_of_two_ne_zero h2 ha hs
  · exact quadratic_formula_minus_of_two_ne_zero h2 ha hs

/-- Exact factorization through the two displayed quadratic-formula values. -/
theorem quadratic_formula_factorization_of_two_ne_zero {a b c s x : K}
    (h2 : (2 : K) ≠ 0) (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
    quadratic a b c x =
      a * (x - (-b + s) / (2 * a)) * (x - (-b - s) / (2 * a)) := by
  unfold quadratic
  field_simp [h2, ha]
  linear_combination hs

/-- Exhaustiveness of the two displayed roots; the roots may coincide. -/
theorem quadratic_eq_zero_iff_of_two_ne_zero {a b c s x : K}
    (h2 : (2 : K) ≠ 0) (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
    quadratic a b c x = 0 ↔
      x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by
  rw [quadratic_formula_factorization_of_two_ne_zero h2 ha hs]
  simp only [mul_eq_zero, ha, false_or, sub_eq_zero]

/-- Monic specialization under the exact hypothesis `2 ≠ 0`. -/
theorem monic_quadratic_eq_zero_iff_of_two_ne_zero {b c s x : K}
    (h2 : (2 : K) ≠ 0) (hs : s ^ 2 = b ^ 2 - 4 * c) :
    x ^ 2 + b * x + c = 0 ↔
      x = (-b + s) / 2 ∨ x = (-b - s) / 2 := by
  simpa [quadratic] using
    (quadratic_eq_zero_iff_of_two_ne_zero
      (a := (1 : K)) (b := b) (c := c) (s := s) (x := x)
      h2 one_ne_zero (by simpa using hs))

end Field

end LeanProofs.PolynomialFormulas
