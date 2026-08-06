import PolynomialFormulas.AbelRuffini
import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Tactic

/-!
# Explicit radicals over the Gaussian rationals

This file supplies the shared data layer for coefficient-only formulas through
degree four.  Gaussian rationals are represented by the quadratic algebra
`ℚ[I]`, and `ExplicitRadical` packages a complex value together with an actual
term in the radical-expression syntax from `PolynomialFormulas.AbelRuffini`.

The radical selectors below are noncomputable choices in `ℂ`.  Their defining
power equations are stored in the syntax and exposed as simp lemmas; there is
no unproved radical oracle or branch convention.
-/

namespace LeanProofs.PolynomialFormulas

noncomputable section

/-! ## Gaussian rationals and their complex embedding -/

/-- The Gaussian rationals `ℚ[I]`, with `I² = -1`. -/
abbrev GaussianRat := QuadraticAlgebra ℚ (-1) 0

/-- No rational number squares to `-1`; this is the irreducibility fact needed
by the field instance for `QuadraticAlgebra ℚ (-1) 0`. -/
instance gaussianRat_irreducible :
    Fact (∀ r : ℚ, r ^ 2 ≠ (-1 : ℚ) + 0 * r) :=
  ⟨by
    intro r h
    have hr : 0 ≤ r ^ 2 := sq_nonneg r
    norm_num at h
    linarith⟩

namespace GaussianRat

/-- The underlying ring homomorphism sending the quadratic generator to
`Complex.I`.  This is the coordinate form of `QuadraticAlgebra.lift`; spelling
it out avoids the instance diamond between the quadratic-algebra and
field-induced `ℚ`-algebra structures. -/
private def toComplexRingHom : GaussianRat →+* ℂ :=
  { toFun := fun z => (z.re : ℂ) + (z.im : ℂ) * Complex.I
    map_zero' := by simp
    map_one' := by
      change ((1 : ℚ) : ℂ) + ((0 : ℚ) : ℂ) * Complex.I = 1
      norm_num
    map_add' := by
      intro x y
      simp
      ring
    map_mul' := by
      intro x y
      simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
      push_cast
      rw [show (-1 : ℂ) = Complex.I * Complex.I by
        exact Complex.I_mul_I.symm]
      ring }

/-- The canonical `ℚ`-algebra embedding `a + bI ↦ a + b Complex.I`. -/
def toComplex : GaussianRat →ₐ[ℚ] ℂ where
  toRingHom := toComplexRingHom
  commutes' q := by
    simp [toComplexRingHom]

theorem toComplex_apply (z : GaussianRat) :
    toComplex z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
  rfl

@[simp]
theorem toComplex_mk (a b : ℚ) :
    toComplex (⟨a, b⟩ : GaussianRat) = (a : ℂ) + (b : ℂ) * Complex.I := by
  simpa using toComplex_apply (⟨a, b⟩ : GaussianRat)

theorem toComplex_injective : Function.Injective toComplex :=
  RingHom.injective toComplex.toRingHom

@[simp]
theorem toComplex_eq_zero {z : GaussianRat} : toComplex z = 0 ↔ z = 0 :=
  map_eq_zero_iff toComplex toComplex_injective

@[simp]
theorem toComplex_ne_zero {z : GaussianRat} : toComplex z ≠ 0 ↔ z ≠ 0 :=
  map_ne_zero_iff toComplex toComplex_injective

theorem toComplex_ne_zero_of_ne_zero {z : GaussianRat} (hz : z ≠ 0) :
    toComplex z ≠ 0 :=
  toComplex_ne_zero.mpr hz

@[simp] theorem toComplex_zero : toComplex 0 = 0 := map_zero toComplex
@[simp] theorem toComplex_one : toComplex 1 = 1 := map_one toComplex
@[simp] theorem toComplex_natCast (n : ℕ) :
    toComplex (n : GaussianRat) = (n : ℂ) := map_natCast toComplex n
@[simp] theorem toComplex_ofNat (n : ℕ) [n.AtLeastTwo] :
    toComplex (ofNat(n) : GaussianRat) = (ofNat(n) : ℂ) := by
  rw [toComplex_apply]
  simp [QuadraticAlgebra.re_ofNat, QuadraticAlgebra.im_ofNat]
@[simp] theorem toComplex_intCast (n : ℤ) :
    toComplex (n : GaussianRat) = (n : ℂ) := map_intCast toComplex n
@[simp] theorem toComplex_ratCast (q : ℚ) :
    toComplex (q : GaussianRat) = (q : ℂ) := map_ratCast toComplex q
@[simp] theorem toComplex_add (x y : GaussianRat) :
    toComplex (x + y) = toComplex x + toComplex y := map_add toComplex x y
@[simp] theorem toComplex_sub (x y : GaussianRat) :
    toComplex (x - y) = toComplex x - toComplex y := map_sub toComplex x y
@[simp] theorem toComplex_neg (x : GaussianRat) :
    toComplex (-x) = -toComplex x := map_neg toComplex x
@[simp] theorem toComplex_mul (x y : GaussianRat) :
    toComplex (x * y) = toComplex x * toComplex y := map_mul toComplex x y
@[simp] theorem toComplex_inv (x : GaussianRat) :
    toComplex x⁻¹ = (toComplex x)⁻¹ := map_inv₀ toComplex x
@[simp] theorem toComplex_div (x y : GaussianRat) :
    toComplex (x / y) = toComplex x / toComplex y := map_div₀ toComplex x y
@[simp] theorem toComplex_pow (x : GaussianRat) (n : ℕ) :
    toComplex (x ^ n) = toComplex x ^ n := map_pow toComplex x n

end GaussianRat

/-! ## Proof-carrying explicit radical values -/

/-- A complex number together with an explicit expression for it using
rational constants, field operations, and chosen positive-order radicals. -/
structure ExplicitRadical where
  value : ℂ
  expression : RadicalExpression value

namespace ExplicitRadical

instance : Coe ExplicitRadical ℂ := ⟨value⟩

@[simp]
theorem coe_mk (z : ℂ) (e : RadicalExpression z) :
    ((⟨z, e⟩ : ExplicitRadical) : ℂ) = z := rfl

/-- A rational constant as an explicit radical expression. -/
def rational (q : ℚ) : ExplicitRadical :=
  ⟨algebraMap ℚ ℂ q, .rational q⟩

/-- Addition of explicit expressions. -/
def add (x y : ExplicitRadical) : ExplicitRadical :=
  ⟨x.value + y.value, .add x.expression y.expression⟩

/-- Subtraction of explicit expressions. -/
def sub (x y : ExplicitRadical) : ExplicitRadical :=
  ⟨x.value - y.value, .sub x.expression y.expression⟩

/-- Negation, represented as subtraction from rational zero. -/
def neg (x : ExplicitRadical) : ExplicitRadical :=
  sub (rational 0) x

/-- Multiplication of explicit expressions. -/
def mul (x y : ExplicitRadical) : ExplicitRadical :=
  ⟨x.value * y.value, .mul x.expression y.expression⟩

/-- Multiplicative inversion of an explicit expression. -/
def inv (x : ExplicitRadical) : ExplicitRadical :=
  ⟨x.value⁻¹, .inv x.expression⟩

/-- Division of explicit expressions. -/
def div (x y : ExplicitRadical) : ExplicitRadical :=
  mul x (inv y)

/-- A natural power, expanded into multiplication in the expression tree. -/
def pow (x : ExplicitRadical) : ℕ → ExplicitRadical
  | 0 => rational 1
  | n + 1 => mul (pow x n) x

instance : Zero ExplicitRadical := ⟨rational 0⟩
instance : One ExplicitRadical := ⟨rational 1⟩
instance : Add ExplicitRadical := ⟨add⟩
instance : Sub ExplicitRadical := ⟨sub⟩
instance : Neg ExplicitRadical := ⟨neg⟩
instance : Mul ExplicitRadical := ⟨mul⟩
instance : Inv ExplicitRadical := ⟨inv⟩
instance : Div ExplicitRadical := ⟨div⟩
instance : Pow ExplicitRadical ℕ := ⟨pow⟩

@[simp] theorem value_rational (q : ℚ) : (rational q).value = (q : ℂ) := rfl
@[simp] theorem value_zero : (0 : ExplicitRadical).value = 0 := by
  change (rational 0).value = 0
  simp
@[simp] theorem value_one : (1 : ExplicitRadical).value = 1 := by
  change (rational 1).value = 1
  simp
@[simp] theorem value_add (x y : ExplicitRadical) : (x + y).value = x.value + y.value := rfl
@[simp] theorem value_sub (x y : ExplicitRadical) : (x - y).value = x.value - y.value := rfl
@[simp] theorem value_neg (x : ExplicitRadical) : (-x).value = -x.value := by
  change (neg x).value = -x.value
  simp [neg, sub]
@[simp] theorem value_mul (x y : ExplicitRadical) : (x * y).value = x.value * y.value := rfl
@[simp] theorem value_inv (x : ExplicitRadical) : x⁻¹.value = x.value⁻¹ := rfl
@[simp] theorem value_div (x y : ExplicitRadical) : (x / y).value = x.value / y.value := rfl

@[simp]
theorem value_pow (x : ExplicitRadical) (n : ℕ) : (x ^ n).value = x.value ^ n := by
  change (pow x n).value = x.value ^ n
  induction n with
  | zero => simp [pow]
  | succ n ih =>
      change (pow x n).value * x.value = x.value ^ (n + 1)
      rw [ih, pow_succ]

/-- A fixed explicit square root of `-1`. -/
def imaginaryUnit : ExplicitRadical :=
  ⟨Complex.I,
    .nthRoot 2 (by decide) Complex.I
      (by simp [Complex.I_sq]) (.rational (-1))⟩

@[simp] theorem value_imaginaryUnit : imaginaryUnit.value = Complex.I := rfl

/-- Turn `a + bI ∈ ℚ[I]` into an expression over rational constants. -/
def ofGaussian (z : GaussianRat) : ExplicitRadical :=
  rational z.re + rational z.im * imaginaryUnit

@[simp]
theorem value_ofGaussian (z : GaussianRat) :
    (ofGaussian z).value = GaussianRat.toComplex z := by
  simp [ofGaussian, GaussianRat.toComplex_apply]

/-- A chosen `n`th root in `ℂ`, packaged with its defining equation. -/
private noncomputable def rootChoice (n : ℕ) (hn : n ≠ 0) (z : ℂ) :
    {w : ℂ // w ^ n = z} := by
  let h := IsAlgClosed.exists_pow_nat_eq z (Nat.pos_of_ne_zero hn)
  exact ⟨Classical.choose h, Classical.choose_spec h⟩

/-- Adjoin a chosen positive-order radical to an explicit expression. -/
noncomputable def nthRoot (n : ℕ) (hn : n ≠ 0)
    (x : ExplicitRadical) : ExplicitRadical :=
  let w := rootChoice n hn x.value
  ⟨w, .nthRoot n hn w w.property x.expression⟩

@[simp]
theorem nthRoot_value_pow (n : ℕ) (hn : n ≠ 0) (x : ExplicitRadical) :
    (nthRoot n hn x).value ^ n = x.value := by
  exact (rootChoice n hn x.value).property

/-- A chosen square root. -/
noncomputable def squareRoot (x : ExplicitRadical) : ExplicitRadical :=
  nthRoot 2 (by decide) x

/-- A chosen cube root. -/
noncomputable def cubeRoot (x : ExplicitRadical) : ExplicitRadical :=
  nthRoot 3 (by decide) x

@[simp]
theorem squareRoot_value_sq (x : ExplicitRadical) :
    (squareRoot x).value ^ 2 = x.value := by
  exact nthRoot_value_pow 2 (by decide) x

@[simp]
theorem cubeRoot_value_cube (x : ExplicitRadical) :
    (cubeRoot x).value ^ 3 = x.value := by
  exact nthRoot_value_pow 3 (by decide) x

/-- The radical expression `(-1 + √(-3)) / 2`. -/
noncomputable def primitiveCubeRoot : ExplicitRadical :=
  (rational (-1) + squareRoot (rational (-3))) / rational 2

/-- The displayed expression is a nontrivial cube root of unity in the form
needed by Cardano's formula. -/
theorem primitiveCubeRoot_spec :
    primitiveCubeRoot.value ^ 2 + primitiveCubeRoot.value + 1 = 0 := by
  have hs := squareRoot_value_sq (rational (-3))
  simp only [value_rational] at hs
  simp only [primitiveCubeRoot, value_div, value_add, value_rational]
  field_simp
  linear_combination hs

theorem primitiveCubeRoot_cubed : primitiveCubeRoot.value ^ 3 = 1 := by
  apply sub_eq_zero.mp
  calc
    primitiveCubeRoot.value ^ 3 - 1 =
        (primitiveCubeRoot.value - 1) *
          (primitiveCubeRoot.value ^ 2 + primitiveCubeRoot.value + 1) := by ring
    _ = 0 := by rw [primitiveCubeRoot_spec]; ring

end ExplicitRadical

end

end LeanProofs.PolynomialFormulas
