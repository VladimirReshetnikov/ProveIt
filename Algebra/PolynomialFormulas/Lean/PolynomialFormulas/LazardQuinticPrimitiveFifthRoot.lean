import PolynomialFormulas.GaussianRadicals
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# A primitive fifth root of unity using square radicals

Lazard counts the primitive fifth root of unity among the square-radical
part of his construction.  This module records the first classical expression

`(-1 + sqrt(5) + sqrt(-10 - 2 sqrt(5))) / 4`

as literal `RadicalExpression` syntax and proves, from the two displayed
square equations, that its value is a primitive fifth root of unity.  It also
records the other three nested-square strings from the paper, proves the
coherent sign relation between their two nested radicals, and verifies their
printed power order `1, 4, 2, 3`.
-/

namespace LeanProofs.PolynomialFormulas

noncomputable section

/-- The positive real square root of five, viewed in `ℂ`. -/
def lazardSqrtFive : ℂ := (Real.sqrt 5 : ℂ)

/-- The square root with positive imaginary part used in the classical
square-radical expression for `exp(2 pi i / 5)`. -/
def lazardSqrtNegativeTenSubTwoSqrtFive : ℂ :=
  Complex.I * (Real.sqrt (10 + 2 * Real.sqrt 5) : ℂ)

/-- The positive-imaginary determination of the other nested square root in
Lazard's four-value display. -/
def lazardSqrtNegativeTenAddTwoSqrtFive : ℂ :=
  Complex.I * (Real.sqrt (10 - 2 * Real.sqrt 5) : ℂ)

/-- Lazard's primitive fifth root, expressed using two square roots. -/
def squareRadicalPrimitiveFifthRoot : ℂ :=
  (-1 + lazardSqrtFive + lazardSqrtNegativeTenSubTwoSqrtFive) * (4 : ℂ)⁻¹

/-- The second value in Lazard's printed order.  It will be the fourth power
of `squareRadicalPrimitiveFifthRoot`. -/
def squareRadicalPrimitiveFifthRootPowFour : ℂ :=
  (-1 + lazardSqrtFive - lazardSqrtNegativeTenSubTwoSqrtFive) * (4 : ℂ)⁻¹

/-- The third value in Lazard's printed order.  It will be the second power
of `squareRadicalPrimitiveFifthRoot`. -/
def squareRadicalPrimitiveFifthRootPowTwo : ℂ :=
  (-1 - lazardSqrtFive + lazardSqrtNegativeTenAddTwoSqrtFive) * (4 : ℂ)⁻¹

/-- The fourth value in Lazard's printed order.  It will be the third power
of `squareRadicalPrimitiveFifthRoot`. -/
def squareRadicalPrimitiveFifthRootPowThree : ℂ :=
  (-1 - lazardSqrtFive - lazardSqrtNegativeTenAddTwoSqrtFive) * (4 : ℂ)⁻¹

theorem lazardSqrtFive_sq : lazardSqrtFive ^ 2 = 5 := by
  rw [lazardSqrtFive, ← Complex.ofReal_pow]
  norm_num [Real.sq_sqrt]

theorem lazardSqrtNegativeTenSubTwoSqrtFive_sq :
    lazardSqrtNegativeTenSubTwoSqrtFive ^ 2 = -10 - 2 * lazardSqrtFive := by
  rw [lazardSqrtNegativeTenSubTwoSqrtFive, mul_pow, Complex.I_sq]
  rw [← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]
  simp [lazardSqrtFive]
  ring

theorem lazardTenSubTwoSqrtFive_nonneg :
    0 ≤ (10 - 2 * Real.sqrt 5 : ℝ) := by
  have hs_le_five : Real.sqrt 5 ≤ 5 := by
    rw [Real.sqrt_le_iff]
    norm_num
  linarith

theorem lazardSqrtNegativeTenAddTwoSqrtFive_sq :
    lazardSqrtNegativeTenAddTwoSqrtFive ^ 2 = -10 + 2 * lazardSqrtFive := by
  rw [lazardSqrtNegativeTenAddTwoSqrtFive, mul_pow, Complex.I_sq]
  rw [← Complex.ofReal_pow,
    Real.sq_sqrt lazardTenSubTwoSqrtFive_nonneg]
  simp [lazardSqrtFive]
  ring

/-- The two independently printed nested radicals are given coherent
determinations: the positive-imaginary square root of `-10 + 2 sqrt(5)` is
forced by the first one.  This is the branch identity that a simplifier must
respect when it replaces the last two printed values by powers of the first. -/
theorem lazardSqrtNegativeTenAddTwoSqrtFive_coherent :
    lazardSqrtNegativeTenAddTwoSqrtFive =
      (lazardSqrtFive - 1) *
        lazardSqrtNegativeTenSubTwoSqrtFive * (2 : ℂ)⁻¹ := by
  have hsSq : (Real.sqrt 5) ^ 2 = (5 : ℝ) :=
    Real.sq_sqrt (by norm_num)
  have hsOne : (1 : ℝ) ≤ Real.sqrt 5 :=
    Real.one_le_sqrt.mpr (by norm_num)
  have hplus : 0 ≤ (10 + 2 * Real.sqrt 5 : ℝ) := by positivity
  have hleft :
      0 ≤ (Real.sqrt 5 - 1) * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 := by
    positivity
  have hsquares :
      ((Real.sqrt 5 - 1) * Real.sqrt (10 + 2 * Real.sqrt 5) / 2) ^ 2 =
        (Real.sqrt (10 - 2 * Real.sqrt 5)) ^ 2 := by
    rw [div_pow, mul_pow, Real.sq_sqrt hplus,
      Real.sq_sqrt lazardTenSubTwoSqrtFive_nonneg]
    field_simp
    linear_combination (2 * Real.sqrt 5 + 6) * hsSq
  have hreal :
      Real.sqrt (10 - 2 * Real.sqrt 5) =
        (Real.sqrt 5 - 1) * Real.sqrt (10 + 2 * Real.sqrt 5) / 2 :=
    ((sq_eq_sq₀ hleft (Real.sqrt_nonneg _)).mp hsquares).symm
  rw [lazardSqrtNegativeTenAddTwoSqrtFive,
    lazardSqrtNegativeTenSubTwoSqrtFive, lazardSqrtFive]
  apply Complex.ext <;> simp [hreal] <;> ring

/-- Purely algebraic verification of the fifth cyclotomic equation. -/
theorem squareRadicalPrimitiveFifthRoot_cyclotomic :
    squareRadicalPrimitiveFifthRoot ^ 4 +
      squareRadicalPrimitiveFifthRoot ^ 3 +
      squareRadicalPrimitiveFifthRoot ^ 2 +
      squareRadicalPrimitiveFifthRoot + 1 = 0 := by
  let s : ℂ := lazardSqrtFive
  let t : ℂ := lazardSqrtNegativeTenSubTwoSqrtFive
  have hs : s ^ 2 = 5 := lazardSqrtFive_sq
  have ht : t ^ 2 = -10 - 2 * s := lazardSqrtNegativeTenSubTwoSqrtFive_sq
  change ((-1 + s + t) * (4 : ℂ)⁻¹) ^ 4 +
      ((-1 + s + t) * (4 : ℂ)⁻¹) ^ 3 +
      ((-1 + s + t) * (4 : ℂ)⁻¹) ^ 2 +
      ((-1 + s + t) * (4 : ℂ)⁻¹) + 1 = 0
  field_simp
  linear_combination
    (s ^ 2 + 4 * s * t - 12 * s - 8 * t - 41) * hs +
    (t ^ 2 + 4 * s * t + 6 * s ^ 2 - 2 * s) * ht

theorem squareRadicalPrimitiveFifthRoot_pow_five :
    squareRadicalPrimitiveFifthRoot ^ 5 = 1 := by
  have h := squareRadicalPrimitiveFifthRoot_cyclotomic
  apply sub_eq_zero.mp
  calc
    squareRadicalPrimitiveFifthRoot ^ 5 - 1 =
        (squareRadicalPrimitiveFifthRoot - 1) *
          (squareRadicalPrimitiveFifthRoot ^ 4 +
            squareRadicalPrimitiveFifthRoot ^ 3 +
            squareRadicalPrimitiveFifthRoot ^ 2 +
            squareRadicalPrimitiveFifthRoot + 1) := by ring
    _ = 0 := by rw [h, mul_zero]

theorem squareRadicalPrimitiveFifthRoot_ne_one :
    squareRadicalPrimitiveFifthRoot ≠ 1 := by
  intro h
  have him : lazardSqrtNegativeTenSubTwoSqrtFive.im = 0 := by
    have := congrArg Complex.im h
    norm_num [squareRadicalPrimitiveFifthRoot, lazardSqrtFive] at this
    linarith
  have hpos : 0 < lazardSqrtNegativeTenSubTwoSqrtFive.im := by
    rw [lazardSqrtNegativeTenSubTwoSqrtFive]
    simp only [Complex.mul_im, Complex.I_re, Complex.I_im, one_mul,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero]
    positivity
  linarith

theorem squareRadicalPrimitiveFifthRoot_primitive :
    IsPrimitiveRoot squareRadicalPrimitiveFifthRoot 5 := by
  apply isPrimitiveRoot_of_mem_nthRootsFinset (R := ℂ) (p := 5) Nat.prime_five
  · exact (Polynomial.mem_nthRootsFinset (by norm_num) 1).2
      squareRadicalPrimitiveFifthRoot_pow_five
  · exact squareRadicalPrimitiveFifthRoot_ne_one

/-- The second printed nested-square value is the fourth power of the first. -/
theorem squareRadicalPrimitiveFifthRootPowFour_eq_pow_four :
    squareRadicalPrimitiveFifthRootPowFour =
      squareRadicalPrimitiveFifthRoot ^ 4 := by
  have hmul :
      squareRadicalPrimitiveFifthRoot *
          squareRadicalPrimitiveFifthRootPowFour = 1 := by
    rw [squareRadicalPrimitiveFifthRoot,
      squareRadicalPrimitiveFifthRootPowFour]
    field_simp
    ring_nf
    rw [lazardSqrtFive_sq, lazardSqrtNegativeTenSubTwoSqrtFive_sq]
    ring
  have hne : squareRadicalPrimitiveFifthRoot ≠ 0 := by
    intro hzero
    have hpow := squareRadicalPrimitiveFifthRoot_pow_five
    exact (by simpa [hzero] using hpow : False)
  apply (mul_left_cancel₀ hne)
  calc
    squareRadicalPrimitiveFifthRoot *
        squareRadicalPrimitiveFifthRootPowFour = 1 := hmul
    _ = squareRadicalPrimitiveFifthRoot ^ 5 :=
      squareRadicalPrimitiveFifthRoot_pow_five.symm
    _ = squareRadicalPrimitiveFifthRoot *
        squareRadicalPrimitiveFifthRoot ^ 4 := by ring

/-- The third printed nested-square value is the second power of the first. -/
theorem squareRadicalPrimitiveFifthRootPowTwo_eq_pow_two :
    squareRadicalPrimitiveFifthRootPowTwo =
      squareRadicalPrimitiveFifthRoot ^ 2 := by
  rw [squareRadicalPrimitiveFifthRootPowTwo,
    squareRadicalPrimitiveFifthRoot,
    lazardSqrtNegativeTenAddTwoSqrtFive_coherent]
  symm
  field_simp
  ring_nf
  rw [lazardSqrtFive_sq, lazardSqrtNegativeTenSubTwoSqrtFive_sq]
  ring

/-- The fourth printed nested-square value is the third power of the first. -/
theorem squareRadicalPrimitiveFifthRootPowThree_eq_pow_three :
    squareRadicalPrimitiveFifthRootPowThree =
      squareRadicalPrimitiveFifthRoot ^ 3 := by
  rw [squareRadicalPrimitiveFifthRootPowThree,
    squareRadicalPrimitiveFifthRoot,
    lazardSqrtNegativeTenAddTwoSqrtFive_coherent]
  symm
  field_simp
  ring_nf
  have hs3 : lazardSqrtFive ^ 3 = 5 * lazardSqrtFive := by
    calc
      lazardSqrtFive ^ 3 = lazardSqrtFive * lazardSqrtFive ^ 2 := by ring
      _ = lazardSqrtFive * 5 := by rw [lazardSqrtFive_sq]
      _ = 5 * lazardSqrtFive := by ring
  have ht3 : lazardSqrtNegativeTenSubTwoSqrtFive ^ 3 =
      -10 * lazardSqrtNegativeTenSubTwoSqrtFive -
        2 * lazardSqrtFive * lazardSqrtNegativeTenSubTwoSqrtFive := by
    calc
      lazardSqrtNegativeTenSubTwoSqrtFive ^ 3 =
          lazardSqrtNegativeTenSubTwoSqrtFive *
            lazardSqrtNegativeTenSubTwoSqrtFive ^ 2 := by ring
      _ = lazardSqrtNegativeTenSubTwoSqrtFive *
          (-10 - 2 * lazardSqrtFive) := by
        rw [lazardSqrtNegativeTenSubTwoSqrtFive_sq]
      _ = -10 * lazardSqrtNegativeTenSubTwoSqrtFive -
          2 * lazardSqrtFive * lazardSqrtNegativeTenSubTwoSqrtFive := by ring
  have hst2 : lazardSqrtFive *
      lazardSqrtNegativeTenSubTwoSqrtFive ^ 2 =
      -10 * lazardSqrtFive - 2 * lazardSqrtFive ^ 2 := by
    rw [lazardSqrtNegativeTenSubTwoSqrtFive_sq]
    ring
  have hs2t : lazardSqrtFive ^ 2 *
      lazardSqrtNegativeTenSubTwoSqrtFive =
      5 * lazardSqrtNegativeTenSubTwoSqrtFive := by
    rw [lazardSqrtFive_sq]
  rw [hs3, ht3, hst2, hs2t,
    lazardSqrtFive_sq, lazardSqrtNegativeTenSubTwoSqrtFive_sq]
  ring

theorem squareRadicalPrimitiveFifthRootPowFour_primitive :
    IsPrimitiveRoot squareRadicalPrimitiveFifthRootPowFour 5 := by
  rw [squareRadicalPrimitiveFifthRootPowFour_eq_pow_four]
  exact squareRadicalPrimitiveFifthRoot_primitive.pow_of_coprime 4 (by decide)

theorem squareRadicalPrimitiveFifthRootPowTwo_primitive :
    IsPrimitiveRoot squareRadicalPrimitiveFifthRootPowTwo 5 := by
  rw [squareRadicalPrimitiveFifthRootPowTwo_eq_pow_two]
  exact squareRadicalPrimitiveFifthRoot_primitive.pow_of_coprime 2 (by decide)

theorem squareRadicalPrimitiveFifthRootPowThree_primitive :
    IsPrimitiveRoot squareRadicalPrimitiveFifthRootPowThree 5 := by
  rw [squareRadicalPrimitiveFifthRootPowThree_eq_pow_three]
  exact squareRadicalPrimitiveFifthRoot_primitive.pow_of_coprime 3 (by decide)

/-- Literal radical syntax for `sqrt(5)`. -/
def lazardSqrtFiveExpression : RadicalExpression lazardSqrtFive :=
  .nthRoot 2 (by norm_num) lazardSqrtFive lazardSqrtFive_sq (.rational 5)

/-- Literal syntax for the radicand `-10 - 2 sqrt(5)`. -/
def lazardNegativeTenSubTwoSqrtFiveExpression :
    RadicalExpression (-10 - 2 * lazardSqrtFive) := by
  simpa using
    RadicalExpression.sub (.rational (-10))
      (RadicalExpression.mul (.rational 2) lazardSqrtFiveExpression)

/-- Literal syntax for the second square root. -/
def lazardSqrtNegativeTenSubTwoSqrtFiveExpression :
    RadicalExpression lazardSqrtNegativeTenSubTwoSqrtFive :=
  .nthRoot 2 (by norm_num) lazardSqrtNegativeTenSubTwoSqrtFive
    lazardSqrtNegativeTenSubTwoSqrtFive_sq
    lazardNegativeTenSubTwoSqrtFiveExpression

/-- Literal syntax for the radicand `-10 + 2 sqrt(5)`. -/
def lazardNegativeTenAddTwoSqrtFiveExpression :
    RadicalExpression (-10 + 2 * lazardSqrtFive) := by
  simpa using
    RadicalExpression.add (.rational (-10))
      (RadicalExpression.mul (.rational 2) lazardSqrtFiveExpression)

/-- Literal syntax for the coherently selected other nested square root. -/
def lazardSqrtNegativeTenAddTwoSqrtFiveExpression :
    RadicalExpression lazardSqrtNegativeTenAddTwoSqrtFive :=
  .nthRoot 2 (by norm_num) lazardSqrtNegativeTenAddTwoSqrtFive
    lazardSqrtNegativeTenAddTwoSqrtFive_sq
    lazardNegativeTenAddTwoSqrtFiveExpression

/-- The primitive fifth root represented using field operations and exactly
two square-root constructors. -/
def squareRadicalPrimitiveFifthRootExpression :
    RadicalExpression squareRadicalPrimitiveFifthRoot := by
  simpa [squareRadicalPrimitiveFifthRoot] using
    RadicalExpression.mul
      (RadicalExpression.add
        (RadicalExpression.add (.rational (-1)) lazardSqrtFiveExpression)
        lazardSqrtNegativeTenSubTwoSqrtFiveExpression)
      (RadicalExpression.inv (.rational 4))

/-- Literal radical syntax for the second value in Lazard's display. -/
def squareRadicalPrimitiveFifthRootPowFourExpression :
    RadicalExpression squareRadicalPrimitiveFifthRootPowFour := by
  simpa [squareRadicalPrimitiveFifthRootPowFour] using
    RadicalExpression.mul
      (RadicalExpression.sub
        (RadicalExpression.add (.rational (-1)) lazardSqrtFiveExpression)
        lazardSqrtNegativeTenSubTwoSqrtFiveExpression)
      (RadicalExpression.inv (.rational 4))

/-- Literal radical syntax for the third value in Lazard's display. -/
def squareRadicalPrimitiveFifthRootPowTwoExpression :
    RadicalExpression squareRadicalPrimitiveFifthRootPowTwo := by
  simpa [squareRadicalPrimitiveFifthRootPowTwo] using
    RadicalExpression.mul
      (RadicalExpression.add
        (RadicalExpression.sub (.rational (-1)) lazardSqrtFiveExpression)
        lazardSqrtNegativeTenAddTwoSqrtFiveExpression)
      (RadicalExpression.inv (.rational 4))

/-- Literal radical syntax for the fourth value in Lazard's display. -/
def squareRadicalPrimitiveFifthRootPowThreeExpression :
    RadicalExpression squareRadicalPrimitiveFifthRootPowThree := by
  simpa [squareRadicalPrimitiveFifthRootPowThree] using
    RadicalExpression.mul
      (RadicalExpression.sub
        (RadicalExpression.sub (.rational (-1)) lazardSqrtFiveExpression)
        lazardSqrtNegativeTenAddTwoSqrtFiveExpression)
      (RadicalExpression.inv (.rational 4))

/-- The same value packaged for the coefficient-level solvers. -/
def explicitSquareRadicalPrimitiveFifthRoot : ExplicitRadical :=
  ⟨squareRadicalPrimitiveFifthRoot,
    squareRadicalPrimitiveFifthRootExpression⟩

def explicitSquareRadicalPrimitiveFifthRootPowFour : ExplicitRadical :=
  ⟨squareRadicalPrimitiveFifthRootPowFour,
    squareRadicalPrimitiveFifthRootPowFourExpression⟩

def explicitSquareRadicalPrimitiveFifthRootPowTwo : ExplicitRadical :=
  ⟨squareRadicalPrimitiveFifthRootPowTwo,
    squareRadicalPrimitiveFifthRootPowTwoExpression⟩

def explicitSquareRadicalPrimitiveFifthRootPowThree : ExplicitRadical :=
  ⟨squareRadicalPrimitiveFifthRootPowThree,
    squareRadicalPrimitiveFifthRootPowThreeExpression⟩

end

end LeanProofs.PolynomialFormulas
