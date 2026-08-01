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

omit [CharZero K] in
/-- Multiplying a compatible radical pair by reciprocal cube roots of unity
preserves both of Cardano's compatibility equations. -/
theorem cardano_twist {p q u v ζ ξ : K}
    (hu : u ^ 3 + v ^ 3 = -q) (huv : u * v = -p / 3)
    (hζ : ζ ^ 3 = 1) (hξ : ξ ^ 3 = 1) (hζξ : ζ * ξ = 1) :
    (ζ * u) ^ 3 + (ξ * v) ^ 3 = -q ∧
      (ζ * u) * (ξ * v) = -p / 3 := by
  constructor
  · calc
      (ζ * u) ^ 3 + (ξ * v) ^ 3 = ζ ^ 3 * u ^ 3 + ξ ^ 3 * v ^ 3 := by ring
      _ = -q := by rw [hζ, hξ]; simpa using hu
  · calc
      (ζ * u) * (ξ * v) = (ζ * ξ) * (u * v) := by ring
      _ = -p / 3 := by rw [hζξ]; simpa using huv

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

/-- Cardano's argument only needs a compatible pair of cube roots; the
displayed square-root equations are one way of constructing such a pair. -/
theorem cardano_formula_of_compatible_pair {a b c d u v : K} (ha : a ≠ 0)
    (hu : u ^ 3 + v ^ 3 = -cubicQ (b / a) (c / a) (d / a))
    (huv : u * v = -cubicP (b / a) (c / a) / 3) :
    cubic a b c d (u + v - (b / a) / 3) = 0 := by
  rw [cubic_normalization ha, depress_monic_cubic, cardano_depressed hu huv]
  ring

omit [CharZero K] in
/-- The quadratic equation characterizing a primitive cube root of unity
implies the cube-root equation used by the three Cardano branches. -/
theorem primitiveCubeRoot_cubed {ω : K} (hω : ω ^ 2 + ω + 1 = 0) : ω ^ 3 = 1 := by
  apply sub_eq_zero.mp
  calc
    ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) := by ring
    _ = 0 := by rw [hω]; ring

omit [CharZero K] in
/-- A depressed cubic factors through any three roots with the expected
elementary symmetric sums. -/
theorem depressedCubic_factorization {p q r₀ r₁ r₂ y : K}
    (hsum : r₀ + r₁ + r₂ = 0)
    (hpairs : r₀ * r₁ + r₀ * r₂ + r₁ * r₂ = p)
    (hproduct : r₀ * r₁ * r₂ = -q) :
    depressedCubic p q y = (y - r₀) * (y - r₁) * (y - r₂) := by
  unfold depressedCubic
  linear_combination (y ^ 2) * hsum - y * hpairs + hproduct

/-- Cardano's three depressed-cubic values give a complete linear
factorization when `ω` is a primitive cube root of unity. -/
theorem cardano_factorization {p q u v ω y : K}
    (hu : u ^ 3 + v ^ 3 = -q) (huv : u * v = -p / 3)
    (hω : ω ^ 2 + ω + 1 = 0) :
    depressedCubic p q y =
      (y - (u + v)) *
        (y - (ω * u + ω ^ 2 * v)) *
          (y - (ω ^ 2 * u + ω * v)) := by
  let r₀ := u + v
  let r₁ := ω * u + ω ^ 2 * v
  let r₂ := ω ^ 2 * u + ω * v
  have hsum : r₀ + r₁ + r₂ = 0 := by
    dsimp [r₀, r₁, r₂]
    linear_combination (u + v) * hω
  have hpairs : r₀ * r₁ + r₀ * r₂ + r₁ * r₂ = p := by
    dsimp [r₀, r₁, r₂]
    linear_combination
      (u * v * ω ^ 2 + (u ^ 2 - u * v + v ^ 2) * ω + 3 * u * v) * hω -
        3 * huv
  have hproduct : r₀ * r₁ * r₂ = -q := by
    dsimp [r₀, r₁, r₂]
    linear_combination
      ((v * u ^ 2 + v ^ 2 * u) * ω ^ 2 +
        (u ^ 3 + v ^ 3) * ω - (u ^ 3 + v ^ 3)) * hω + hu
  exact depressedCubic_factorization hsum hpairs hproduct

/-- A general cubic is the leading coefficient times the three linear factors
provided by Cardano's formula. -/
theorem cubic_factorization {a b c d s u v ω x : K} (ha : a ≠ 0)
    (hu : u ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 +
      s)
    (hv : v ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 -
      s)
    (huv : u * v = -cubicP (b / a) (c / a) / 3)
    (hω : ω ^ 2 + ω + 1 = 0) :
    cubic a b c d x =
      a * ((x - solveCubic a b c d u v ω 0) *
        (x - solveCubic a b c d u v ω 1) *
          (x - solveCubic a b c d u v ω 2)) := by
  rw [cubic_normalization ha]
  have htranslate :
      monicCubic (b / a) (c / a) (d / a) x =
        depressedCubic (cubicP (b / a) (c / a))
          (cubicQ (b / a) (c / a) (d / a)) (x + (b / a) / 3) := by
    rw [← depress_monic_cubic]
    congr 1
    ring
  rw [htranslate]
  have hsum : u ^ 3 + v ^ 3 = -cubicQ (b / a) (c / a) (d / a) := by
    rw [hu, hv]
    ring
  rw [cardano_factorization hsum huv hω]
  have hr₀ : solveCubic a b c d u v ω 0 = u + v - (b / a) / 3 := by
    simp [solveCubic]
  have hr₁ : solveCubic a b c d u v ω 1 =
      ω * u + ω ^ 2 * v - (b / a) / 3 := by
    simp [solveCubic]
  have hr₂ : solveCubic a b c d u v ω 2 =
      ω ^ 2 * u + ω * v - (b / a) / 3 := by
    simp [solveCubic]
  rw [hr₀, hr₁, hr₂]
  ring

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
  apply cardano_formula_of_compatible_pair ha _ huv
  linear_combination hu + hv

/-- Every entry computed by `solveCubic` is a root of the input cubic. -/
theorem solveCubic_correct {a b c d s u v ω : K} (ha : a ≠ 0)
    (hs : s ^ 2 = cubicDelta (cubicP (b / a) (c / a))
      (cubicQ (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 + s)
    (hv : v ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 - s)
    (huv : u * v = -cubicP (b / a) (c / a) / 3)
    (hω : ω ^ 3 = 1) (i : Fin 3) :
    cubic a b c d (solveCubic a b c d u v ω i) = 0 := by
  have hsum : u ^ 3 + v ^ 3 = -cubicQ (b / a) (c / a) (d / a) := by
    linear_combination hu + hv
  have hω₂ : (ω ^ 2) ^ 3 = 1 := by
    calc
      (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω]; ring
  have hωω₂ : ω * ω ^ 2 = 1 := by
    calc
      ω * ω ^ 2 = ω ^ 3 := by ring
      _ = 1 := hω
  obtain ⟨hsum₁, huv₁⟩ := cardano_twist hsum huv hω hω₂ hωω₂
  obtain ⟨hsum₂, huv₂⟩ := cardano_twist hsum huv hω₂ hω (by
    simpa [mul_comm] using hωω₂)
  fin_cases i
  · exact cardano_formula ha hs hu hv huv
  · exact cardano_formula_of_compatible_pair ha hsum₁ huv₁
  · exact cardano_formula_of_compatible_pair ha hsum₂ huv₂

/-- Every root of the input cubic occurs in `solveCubic` when `ω` is a
primitive cube root of unity. -/
theorem solveCubic_exhaustive {a b c d s u v ω x : K} (ha : a ≠ 0)
    (hu : u ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 + s)
    (hv : v ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 - s)
    (huv : u * v = -cubicP (b / a) (c / a) / 3)
    (hω : ω ^ 2 + ω + 1 = 0)
    (hx : cubic a b c d x = 0) :
    ∃ i, solveCubic a b c d u v ω i = x := by
  rw [cubic_factorization ha hu hv huv hω] at hx
  simp only [mul_eq_zero, ha, false_or, sub_eq_zero] at hx
  rcases hx with (h | h) | h
  · exact ⟨0, h.symm⟩
  · exact ⟨1, h.symm⟩
  · exact ⟨2, h.symm⟩

/-- The Cardano collection contains exactly all roots of the cubic. -/
theorem cubic_eq_zero_iff {a b c d s u v ω x : K} (ha : a ≠ 0)
    (hs : s ^ 2 = cubicDelta (cubicP (b / a) (c / a))
      (cubicQ (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 + s)
    (hv : v ^ 3 = -cubicQ (b / a) (c / a) (d / a) / 2 - s)
    (huv : u * v = -cubicP (b / a) (c / a) / 3)
    (hω : ω ^ 2 + ω + 1 = 0) :
    cubic a b c d x = 0 ↔ ∃ i, solveCubic a b c d u v ω i = x := by
  constructor
  · exact solveCubic_exhaustive ha hu hv huv hω
  · rintro ⟨i, rfl⟩
    exact solveCubic_correct ha hs hu hv huv (primitiveCubeRoot_cubed hω) i

end Field

end LeanProofs.PolynomialFormulas
