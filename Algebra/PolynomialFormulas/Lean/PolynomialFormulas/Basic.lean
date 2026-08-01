import Mathlib.Tactic

/-!
# The linear and quadratic formulas

The statements are field-generic.  A square root is represented by an element
`s` together with the equation that it squares to the discriminant; no choice
of an analytic square-root branch is hidden in the formalization.
-/

namespace LeanProofs.PolynomialFormulas

section Field

variable {K : Type*} [Field K]

/-- Evaluation of `a x + b`. -/
def linear (a b x : K) : K := a * x + b

/-- The linear formula evaluates to a root when the leading coefficient is nonzero. -/
theorem linear_formula {a b : K} (ha : a ≠ 0) :
    linear a b (-b / a) = 0 := by
  unfold linear
  field_simp [ha]
  ring

/-- Executable expression for the root of a linear equation. -/
def solveLinear (a b : K) : K := -b / a

/-- The linear solver always returns the unique root when `a ≠ 0`. -/
theorem solveLinear_correct {a b : K} (ha : a ≠ 0) :
    linear a b (solveLinear a b) = 0 := by
  exact linear_formula ha

/-- The linear formula gives the unique root. -/
theorem linear_eq_zero_iff {a b x : K} (ha : a ≠ 0) :
    linear a b x = 0 ↔ x = -b / a := by
  constructor
  · intro h
    apply (eq_div_iff ha).2
    simpa [linear, mul_comm] using congrArg (fun z => z - b) h
  · rintro rfl
    exact linear_formula ha

/-- Evaluation of `a x² + b x + c`. -/
def quadratic (a b c x : K) : K := a * x ^ 2 + b * x + c

variable [CharZero K]

/-- The two values computed by the quadratic formula. -/
def solveQuadratic (a b _c s : K) : Fin 2 → K :=
  ![(-b + s) / (2 * a), (-b - s) / (2 * a)]

/-- The `+` branch of the quadratic formula. -/
theorem quadratic_formula_plus {a b c s : K} (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
    quadratic a b c ((-b + s) / (2 * a)) = 0 := by
  unfold quadratic
  field_simp [ha]
  linear_combination hs

/-- The `-` branch of the quadratic formula. -/
theorem quadratic_formula_minus {a b c s : K} (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
    quadratic a b c ((-b - s) / (2 * a)) = 0 := by
  simpa [sub_eq_add_neg] using
    (quadratic_formula_plus (s := -s) ha (by simpa using hs))

/-- Every entry returned by `solveQuadratic` is a root. -/
theorem solveQuadratic_correct {a b c s : K} (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) (i : Fin 2) :
    quadratic a b c (solveQuadratic a b c s i) = 0 := by
  fin_cases i
  · exact quadratic_formula_plus ha hs
  · exact quadratic_formula_minus ha hs

/-- The quadratic polynomial factors through the two formula roots. -/
theorem quadratic_formula_factorization {a b c s x : K} (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
    quadratic a b c x =
      a * (x - (-b + s) / (2 * a)) * (x - (-b - s) / (2 * a)) := by
  unfold quadratic
  field_simp [ha]
  linear_combination hs

/-- Every root is one of the two values supplied by the quadratic formula. -/
theorem quadratic_eq_zero_iff {a b c s x : K} (ha : a ≠ 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
    quadratic a b c x = 0 ↔
      x = (-b + s) / (2 * a) ∨ x = (-b - s) / (2 * a) := by
  rw [quadratic_formula_factorization ha hs]
  simp only [mul_eq_zero, ha, false_or, sub_eq_zero]

/-- Monic specialization of the quadratic root characterization, convenient
when a larger polynomial has been factored into monic quadratics. -/
theorem monic_quadratic_eq_zero_iff {b c s x : K}
    (hs : s ^ 2 = b ^ 2 - 4 * c) :
    x ^ 2 + b * x + c = 0 ↔
      x = (-b + s) / 2 ∨ x = (-b - s) / 2 := by
  simpa [quadratic] using
    (quadratic_eq_zero_iff (a := (1 : K)) (b := b) (c := c) (s := s) (x := x)
      one_ne_zero (by simpa using hs))

end Field

end LeanProofs.PolynomialFormulas
