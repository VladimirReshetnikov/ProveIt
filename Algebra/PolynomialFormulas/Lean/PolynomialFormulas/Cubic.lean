import PolynomialFormulas.Basic

/-!
# Cardano's cubic formula

The proof first translates a monic cubic to depressed form, then verifies the
two compatible cube radicals.  A final theorem combines this with division by
the original leading coefficient.
-/

namespace LeanProofs.PolynomialFormulas

section Field

variable {K : Type*} [Field K]

/-- Evaluation of `a x³ + b x² + c x + d`. -/
def cubic (a b c d x : K) : K := a * x ^ 3 + b * x ^ 2 + c * x + d

/-- Evaluation of the monic cubic `x³ + A x² + B x + C`. -/
def monicCubic (A B C x : K) : K := x ^ 3 + A * x ^ 2 + B * x + C

/-- Evaluation of the depressed cubic `y³ + p y + q`. -/
def depressedCubic (p q y : K) : K := y ^ 3 + p * y + q

/-- The linear coefficient after translating `x = y - A/3`. -/
def cubicP (A B : K) : K := B - 3 * (A / 3) ^ 2

/-- The constant coefficient after translating `x = y - A/3`. -/
def cubicQ (A B C : K) : K := C - B * (A / 3) + 2 * (A / 3) ^ 3

/-- Cardano's discriminant for the depressed cubic. -/
def cubicDelta (p q : K) : K := (q / 2) ^ 2 + (p / 3) ^ 3

/-- The three Cardano values obtained by multiplying compatible cube roots by
the three powers of a cube root of unity. -/
def solveCubic (a b _c _d u v ω : K) : Fin 3 → K :=
  ![u + v - (b / a) / 3,
    ω * u + ω ^ 2 * v - (b / a) / 3,
    ω ^ 2 * u + ω * v - (b / a) / 3]

/-- Dividing by the leading coefficient turns a general cubic into a monic one. -/
theorem cubic_normalization {a b c d x : K} (ha : a ≠ 0) :
    cubic a b c d x = a * monicCubic (b / a) (c / a) (d / a) x := by
  unfold cubic monicCubic
  field_simp [ha]

variable [CharZero K]

/-- Translating a monic cubic by `A/3` removes its quadratic term. -/
theorem depress_monic_cubic (A B C y : K) :
    monicCubic A B C (y - A / 3) = depressedCubic (cubicP A B) (cubicQ A B C) y := by
  unfold monicCubic depressedCubic cubicP cubicQ
  ring

/-- Compatible cube roots solve the depressed cubic. -/
theorem cardano_depressed {p q u v : K}
    (hu : u ^ 3 + v ^ 3 = -q) (huv : u * v = -p / 3) :
    depressedCubic p q (u + v) = 0 := by
  unfold depressedCubic
  linear_combination hu + (3 * (u + v)) * huv

/-- The two radicals occurring in Cardano's displayed formula are compatible
exactly when their product is `-p/3`; under that branch condition their sum is
a root. -/
theorem cardano_radical_pair {p q s u v : K}
    (hu : u ^ 3 = -q / 2 + s) (hv : v ^ 3 = -q / 2 - s)
    (huv : u * v = -p / 3) :
    depressedCubic p q (u + v) = 0 := by
  apply cardano_depressed _ huv
  linear_combination hu + hv

/-- The square radical in Cardano's formula has the classical discriminant. -/
theorem cardano_discriminant_equation {p q s : K}
    (hs : s ^ 2 = cubicDelta p q) :
    (-q / 2 + s) * (-q / 2 - s) = -(p / 3) ^ 3 := by
  unfold cubicDelta at hs
  linear_combination -hs

/-- Cardano's formula for an arbitrary cubic with nonzero leading coefficient.

`s` is the square radical and `u`, `v` are the two cube radicals.  The product
hypothesis records the standard compatible choice of cube-root branches.
-/
theorem cardano_formula {a b c d s u v : K} (ha : a ≠ 0)
    (_hs : s ^ 2 = cubicDelta (cubicP (b / a) (c / a))
      (cubicQ (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 + s)
    (hv : v ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 - s)
    (huv : u * v = -cubicP (b / a) (c / a) / 3) :
    cubic a b c d (u + v - (b / a) / 3) = 0 := by
  rw [cubic_normalization ha]
  rw [depress_monic_cubic]
  rw [cardano_radical_pair hu hv huv]
  ring

/-- Every entry computed by `solveCubic` is a root of the input cubic. -/
theorem solveCubic_correct {a b c d s u v ω : K} (ha : a ≠ 0)
    (hs : s ^ 2 = cubicDelta (cubicP (b / a) (c / a))
      (cubicQ (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 + s)
    (hv : v ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 - s)
    (huv : u * v = -cubicP (b / a) (c / a) / 3)
    (hω : ω ^ 3 = 1) (i : Fin 3) :
    cubic a b c d (solveCubic a b c d u v ω i) = 0 := by
  have hω₂ : (ω ^ 2) ^ 3 = 1 := by
    calc
      (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω]; ring
  have hu₁ : (ω * u) ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 + s := by
    calc
      (ω * u) ^ 3 = ω ^ 3 * u ^ 3 := by ring
      _ = _ := by rw [hω, hu]; ring
  have hv₁ : (ω ^ 2 * v) ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 - s := by
    calc
      (ω ^ 2 * v) ^ 3 = (ω ^ 2) ^ 3 * v ^ 3 := by ring
      _ = _ := by rw [hω₂, hv]; ring
  have huv₁ : (ω * u) * (ω ^ 2 * v) = -cubicP (b / a) (c / a) / 3 := by
    calc
      (ω * u) * (ω ^ 2 * v) = ω ^ 3 * (u * v) := by ring
      _ = _ := by rw [hω, huv]; ring
  have hu₂ : (ω ^ 2 * u) ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 + s := by
    calc
      (ω ^ 2 * u) ^ 3 = (ω ^ 2) ^ 3 * u ^ 3 := by ring
      _ = _ := by rw [hω₂, hu]; ring
  have hv₂ : (ω * v) ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 - s := by
    calc
      (ω * v) ^ 3 = ω ^ 3 * v ^ 3 := by ring
      _ = _ := by rw [hω, hv]; ring
  have huv₂ : (ω ^ 2 * u) * (ω * v) = -cubicP (b / a) (c / a) / 3 := by
    calc
      (ω ^ 2 * u) * (ω * v) = ω ^ 3 * (u * v) := by ring
      _ = _ := by rw [hω, huv]; ring
  fin_cases i
  · exact cardano_formula ha hs hu hv huv
  · exact cardano_formula ha hs hu₁ hv₁ huv₁
  · exact cardano_formula ha hs hu₂ hv₂ huv₂

end Field

end LeanProofs.PolynomialFormulas
