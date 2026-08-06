import PolynomialFormulas.Cubic
import PolynomialFormulas.GaussianRadicals

/-!
# Coefficient-only quadratic and cubic formulas over the Gaussian rationals

This module turns the conditional formula APIs in `Basic` and `Cubic` into
coefficient-only constructions over `GaussianRat`.  The outputs are actual
`ExplicitRadical` values, so each complex value is accompanied by a term in
the radical-expression syntax.

The cubic construction branches only on whether the depressed Gaussian
coefficient `p` is zero.  In the zero case it solves `y^3 + q` directly.  In
the nonzero case it chooses one Cardano cube root and defines the other by the
product condition; this avoids testing equality of chosen complex radicals.
-/

namespace LeanProofs.PolynomialFormulas

noncomputable section

namespace GaussianCubicSolver

open ExplicitRadical

/-! ## Gaussian normalization -/

/-- The depressed linear coefficient of a Gaussian-rational cubic. -/
def normalizedCubicP (a b c : GaussianRat) : GaussianRat :=
  cubicP (b / a) (c / a)

/-- The depressed constant coefficient of a Gaussian-rational cubic. -/
def normalizedCubicQ (a b c d : GaussianRat) : GaussianRat :=
  cubicQ (b / a) (c / a) (d / a)

/-- Cardano's discriminant, computed before embedding into `ℂ`. -/
def normalizedCubicDelta (a b c d : GaussianRat) : GaussianRat :=
  cubicDelta (normalizedCubicP a b c) (normalizedCubicQ a b c d)

/-- The quadratic discriminant, computed in the Gaussian rationals. -/
def quadraticDiscriminant (a b c : GaussianRat) : GaussianRat :=
  b ^ 2 - 4 * a * c

@[simp]
theorem toComplex_normalizedCubicP (a b c : GaussianRat) :
    GaussianRat.toComplex (normalizedCubicP a b c) =
      cubicP (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a) := by
  simp [normalizedCubicP, cubicP]

@[simp]
theorem toComplex_normalizedCubicQ (a b c d : GaussianRat) :
    GaussianRat.toComplex (normalizedCubicQ a b c d) =
      cubicQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a)
        (GaussianRat.toComplex d / GaussianRat.toComplex a) := by
  simp [normalizedCubicQ, cubicQ]

@[simp]
theorem toComplex_normalizedCubicDelta (a b c d : GaussianRat) :
    GaussianRat.toComplex (normalizedCubicDelta a b c d) =
      cubicDelta
        (cubicP (GaussianRat.toComplex b / GaussianRat.toComplex a)
          (GaussianRat.toComplex c / GaussianRat.toComplex a))
        (cubicQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
          (GaussianRat.toComplex c / GaussianRat.toComplex a)
          (GaussianRat.toComplex d / GaussianRat.toComplex a)) := by
  simp [normalizedCubicDelta, cubicDelta]

@[simp]
theorem toComplex_quadraticDiscriminant (a b c : GaussianRat) :
    GaussianRat.toComplex (quadraticDiscriminant a b c) =
      GaussianRat.toComplex b ^ 2 -
        4 * GaussianRat.toComplex a * GaussianRat.toComplex c := by
  simp [quadraticDiscriminant]

/-! ## Quadratics -/

/-- The square radical needed by the quadratic formula. -/
structure QuadraticCertificate (a b c : GaussianRat) where
  s : ExplicitRadical
  square : s.value ^ 2 =
    GaussianRat.toComplex b ^ 2 -
      4 * GaussianRat.toComplex a * GaussianRat.toComplex c

/-- Choose the discriminant square root of a Gaussian-rational quadratic. -/
def quadraticCertificate (a b c : GaussianRat) : QuadraticCertificate a b c := by
  let disc := ofGaussian (quadraticDiscriminant a b c)
  let s := squareRoot disc
  refine ⟨s, ?_⟩
  simp [s, disc]

/-- The two quadratic-formula values, each carrying its radical expression. -/
def quadraticRoots (a b c : GaussianRat) : Fin 2 → ExplicitRadical :=
  let w := quadraticCertificate a b c
  ![(ofGaussian (-b) + w.s) / ofGaussian (2 * a),
    (ofGaussian (-b) - w.s) / ofGaussian (2 * a)]

@[simp]
theorem quadraticRoots_value (a b c : GaussianRat) (i : Fin 2) :
    (quadraticRoots a b c i).value =
      solveQuadratic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
        (GaussianRat.toComplex c) (quadraticCertificate a b c).s.value i := by
  fin_cases i <;> simp [quadraticRoots, solveQuadratic]

/-- Every returned quadratic value is a root when the leading coefficient is
nonzero. -/
theorem quadraticRoots_sound {a b c : GaussianRat} (ha : a ≠ 0) (i : Fin 2) :
    quadratic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) (quadraticRoots a b c i).value = 0 := by
  rw [quadraticRoots_value]
  exact solveQuadratic_correct
    (GaussianRat.toComplex_ne_zero_of_ne_zero ha)
    (quadraticCertificate a b c).square i

/-- Every complex root of a genuine Gaussian-rational quadratic occurs in the
two-entry radical collection. -/
theorem quadraticRoots_exhaustive {a b c : GaussianRat} (ha : a ≠ 0) {x : ℂ}
    (hx : quadratic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) x = 0) :
    ∃ i, (quadraticRoots a b c i).value = x := by
  have hiff := LeanProofs.PolynomialFormulas.quadratic_eq_zero_iff
    (K := ℂ) (a := GaussianRat.toComplex a) (b := GaussianRat.toComplex b)
    (c := GaussianRat.toComplex c) (s := (quadraticCertificate a b c).s.value)
    (x := x) (GaussianRat.toComplex_ne_zero_of_ne_zero ha)
    (quadraticCertificate a b c).square
  rcases hiff.mp hx with h | h
  · refine ⟨0, ?_⟩
    rw [quadraticRoots_value]
    simpa [solveQuadratic] using h.symm
  · refine ⟨1, ?_⟩
    rw [quadraticRoots_value]
    simpa [solveQuadratic] using h.symm

/-- Exact root characterization for the coefficient-only quadratic solver. -/
theorem quadratic_eq_zero_iff_roots {a b c : GaussianRat} (ha : a ≠ 0) (x : ℂ) :
    quadratic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) x = 0 ↔
        ∃ i, (quadraticRoots a b c i).value = x := by
  constructor
  · exact quadraticRoots_exhaustive ha
  · rintro ⟨i, rfl⟩
    exact quadraticRoots_sound ha i

/-- The returned radical values give the complete linear factorization of a
genuine Gaussian-rational quadratic. -/
theorem quadraticRoots_factorization {a b c : GaussianRat} (ha : a ≠ 0) (x : ℂ) :
    quadratic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) x =
        GaussianRat.toComplex a *
          (x - (quadraticRoots a b c 0).value) *
            (x - (quadraticRoots a b c 1).value) := by
  rw [quadraticRoots_value, quadraticRoots_value]
  simpa [solveQuadratic] using
    (quadratic_formula_factorization
      (K := ℂ) (a := GaussianRat.toComplex a) (b := GaussianRat.toComplex b)
      (c := GaussianRat.toComplex c) (s := (quadraticCertificate a b c).s.value)
      (x := x) (GaussianRat.toComplex_ne_zero_of_ne_zero ha)
      (quadraticCertificate a b c).square)

/-! ## Cubics -/

/-- The compatible Cardano radicals and the primitive cube root used by the
coefficient-only cubic formula. -/
structure CubicCertificate (a b c d : GaussianRat) where
  s : ExplicitRadical
  u : ExplicitRadical
  v : ExplicitRadical
  omega : ExplicitRadical
  square : s.value ^ 2 =
    cubicDelta (GaussianRat.toComplex (normalizedCubicP a b c))
      (GaussianRat.toComplex (normalizedCubicQ a b c d))
  cubeU : u.value ^ 3 =
    -GaussianRat.toComplex (normalizedCubicQ a b c d) / 2 + s.value
  cubeV : v.value ^ 3 =
    -GaussianRat.toComplex (normalizedCubicQ a b c d) / 2 - s.value
  product : u.value * v.value =
    -GaussianRat.toComplex (normalizedCubicP a b c) / 3
  primitive : omega.value ^ 2 + omega.value + 1 = 0

/-- Construct compatible Cardano radicals.  The only case split is the exact,
decidable test whether the depressed Gaussian coefficient `p` is zero. -/
def cubicCertificate (a b c d : GaussianRat) : CubicCertificate a b c d := by
  classical
  let p := normalizedCubicP a b c
  let q := normalizedCubicQ a b c d
  by_cases hp : p = 0
  · let s := ofGaussian (-q / 2)
    let u := cubeRoot (ofGaussian (-q))
    let v : ExplicitRadical := 0
    let omega := primitiveCubeRoot
    refine
      { s := s
        u := u
        v := v
        omega := omega
        square := ?_
        cubeU := ?_
        cubeV := ?_
        product := ?_
        primitive := primitiveCubeRoot_spec }
    · (simp [s, p, q, hp, cubicDelta]; ring)
    · simp [u, s, q]
    · simp [v, s, q]
    · simp [v, p, hp]
  · let delta := ofGaussian (cubicDelta p q)
    let s := squareRoot delta
    let U := -ofGaussian q / rational 2 + s
    let V := -ofGaussian q / rational 2 - s
    let gamma := -ofGaussian p / rational 3
    let u := cubeRoot U
    have hs : s.value ^ 2 =
        cubicDelta (GaussianRat.toComplex p) (GaussianRat.toComplex q) := by
      simp [s, delta, cubicDelta]
    have hUV : U.value * V.value =
        (-GaussianRat.toComplex p / 3) ^ 3 := by
      calc
        U.value * V.value =
            (-GaussianRat.toComplex q / 2 + s.value) *
              (-GaussianRat.toComplex q / 2 - s.value) := by
                simp [U, V]
        _ = -(GaussianRat.toComplex p / 3) ^ 3 :=
          cardano_discriminant_equation hs
        _ = (-GaussianRat.toComplex p / 3) ^ 3 := by ring
    have hU : U.value ≠ 0 := by
      intro hU0
      have hcube : (-GaussianRat.toComplex p / 3) ^ 3 = 0 := by
        rw [← hUV, hU0, zero_mul]
      have hbase : -GaussianRat.toComplex p / 3 = 0 := by
        by_contra hne
        exact (pow_ne_zero 3 hne) hcube
      have hpC : GaussianRat.toComplex p = 0 := by
        simpa using hbase
      exact hp (GaussianRat.toComplex_injective (by simpa using hpC))
    have hu : u.value ^ 3 = U.value := by
      simp [u]
    have hu0 : u.value ≠ 0 := by
      intro huZero
      apply hU
      rw [← hu, huZero]
      norm_num
    let v := gamma / u
    have hv : v.value ^ 3 = V.value := by
      simp only [v, value_div]
      rw [div_pow]
      apply (div_eq_iff (pow_ne_zero 3 hu0)).2
      rw [hu]
      simpa [gamma, mul_comm] using hUV.symm
    have huv : u.value * v.value = -GaussianRat.toComplex p / 3 := by
      simp only [v, gamma, value_div, value_neg, value_ofGaussian, value_rational]
      field_simp [hu0]
      norm_num
    refine
      { s := s
        u := u
        v := v
        omega := primitiveCubeRoot
        square := by simpa [p, q] using hs
        cubeU := by simpa [p, q, U] using hu
        cubeV := by simpa [p, q, V] using hv
        product := by simpa [p] using huv
        primitive := primitiveCubeRoot_spec }

/-- The three Cardano values, with explicit radical expressions attached. -/
def cubicRoots (a b c d : GaussianRat) : Fin 3 → ExplicitRadical :=
  let w := cubicCertificate a b c d
  let shift := ofGaussian ((b / a) / 3)
  ![w.u + w.v - shift,
    w.omega * w.u + w.omega ^ 2 * w.v - shift,
    w.omega ^ 2 * w.u + w.omega * w.v - shift]

@[simp]
theorem cubicRoots_value (a b c d : GaussianRat) (i : Fin 3) :
    (cubicRoots a b c d i).value =
      solveCubic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
        (GaussianRat.toComplex c) (GaussianRat.toComplex d)
        (cubicCertificate a b c d).u.value
        (cubicCertificate a b c d).v.value
        (cubicCertificate a b c d).omega.value i := by
  fin_cases i <;> simp [cubicRoots, solveCubic]

/-- Every value returned by the coefficient-only cubic solver is a root. -/
theorem cubicRoots_sound {a b c d : GaussianRat} (ha : a ≠ 0) (i : Fin 3) :
    cubic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) (GaussianRat.toComplex d)
      (cubicRoots a b c d i).value = 0 := by
  let w := cubicCertificate a b c d
  have hs : w.s.value ^ 2 =
      cubicDelta
        (cubicP (GaussianRat.toComplex b / GaussianRat.toComplex a)
          (GaussianRat.toComplex c / GaussianRat.toComplex a))
        (cubicQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
          (GaussianRat.toComplex c / GaussianRat.toComplex a)
          (GaussianRat.toComplex d / GaussianRat.toComplex a)) := by
    simpa [w] using w.square
  have hu : w.u.value ^ 3 =
      -cubicQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a)
        (GaussianRat.toComplex d / GaussianRat.toComplex a) / 2 + w.s.value := by
    simpa [w] using w.cubeU
  have hv : w.v.value ^ 3 =
      -cubicQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a)
        (GaussianRat.toComplex d / GaussianRat.toComplex a) / 2 - w.s.value := by
    simpa [w] using w.cubeV
  have huv : w.u.value * w.v.value =
      -cubicP (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a) / 3 := by
    simpa [w] using w.product
  have homega : w.omega.value ^ 3 = 1 :=
    LeanProofs.PolynomialFormulas.primitiveCubeRoot_cubed w.primitive
  rw [cubicRoots_value]
  exact solveCubic_correct
    (GaussianRat.toComplex_ne_zero_of_ne_zero ha) hs hu hv huv homega i

/-- Every complex root of a genuine Gaussian-rational cubic occurs in the
three-entry radical collection. -/
theorem cubicRoots_exhaustive {a b c d : GaussianRat} (ha : a ≠ 0) {x : ℂ}
    (hx : cubic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) (GaussianRat.toComplex d) x = 0) :
    ∃ i, (cubicRoots a b c d i).value = x := by
  let w := cubicCertificate a b c d
  have hu : w.u.value ^ 3 =
      -cubicQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a)
        (GaussianRat.toComplex d / GaussianRat.toComplex a) / 2 + w.s.value := by
    simpa [w] using w.cubeU
  have hv : w.v.value ^ 3 =
      -cubicQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a)
        (GaussianRat.toComplex d / GaussianRat.toComplex a) / 2 - w.s.value := by
    simpa [w] using w.cubeV
  have huv : w.u.value * w.v.value =
      -cubicP (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a) / 3 := by
    simpa [w] using w.product
  obtain ⟨i, hi⟩ := solveCubic_exhaustive
    (s := w.s.value) (u := w.u.value) (v := w.v.value)
    (ω := w.omega.value)
    (GaussianRat.toComplex_ne_zero_of_ne_zero ha) hu hv huv w.primitive hx
  refine ⟨i, ?_⟩
  rw [cubicRoots_value]
  exact hi

/-- Exact root characterization for the coefficient-only cubic solver. -/
theorem cubic_eq_zero_iff_roots {a b c d : GaussianRat} (ha : a ≠ 0) (x : ℂ) :
    cubic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) (GaussianRat.toComplex d) x = 0 ↔
        ∃ i, (cubicRoots a b c d i).value = x := by
  constructor
  · exact cubicRoots_exhaustive ha
  · rintro ⟨i, rfl⟩
    exact cubicRoots_sound ha i

/-- The returned radical values give the complete linear factorization of a
genuine Gaussian-rational cubic. -/
theorem cubicRoots_factorization {a b c d : GaussianRat} (ha : a ≠ 0) (x : ℂ) :
    cubic (GaussianRat.toComplex a) (GaussianRat.toComplex b)
      (GaussianRat.toComplex c) (GaussianRat.toComplex d) x =
        GaussianRat.toComplex a *
          ((x - (cubicRoots a b c d 0).value) *
            (x - (cubicRoots a b c d 1).value) *
              (x - (cubicRoots a b c d 2).value)) := by
  let w := cubicCertificate a b c d
  have hu : w.u.value ^ 3 =
      -cubicQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a)
        (GaussianRat.toComplex d / GaussianRat.toComplex a) / 2 + w.s.value := by
    simpa [w] using w.cubeU
  have hv : w.v.value ^ 3 =
      -cubicQ (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a)
        (GaussianRat.toComplex d / GaussianRat.toComplex a) / 2 - w.s.value := by
    simpa [w] using w.cubeV
  have huv : w.u.value * w.v.value =
      -cubicP (GaussianRat.toComplex b / GaussianRat.toComplex a)
        (GaussianRat.toComplex c / GaussianRat.toComplex a) / 3 := by
    simpa [w] using w.product
  have hfactor := cubic_factorization
    (K := ℂ) (a := GaussianRat.toComplex a) (b := GaussianRat.toComplex b)
    (c := GaussianRat.toComplex c) (d := GaussianRat.toComplex d)
    (s := w.s.value) (u := w.u.value) (v := w.v.value) (ω := w.omega.value)
    (x := x) (GaussianRat.toComplex_ne_zero_of_ne_zero ha)
    hu hv huv w.primitive
  rw [cubicRoots_value, cubicRoots_value, cubicRoots_value]
  simpa [w] using hfactor

end GaussianCubicSolver

end

end LeanProofs.PolynomialFormulas
