import PolynomialFormulas.GaussianQuarticSolver

/-!
# A total radical solver for Gaussian-rational polynomials of degree at most four

The input stores all five coefficients, including possible zero leading
coefficients.  `solve` dispatches to the coefficient-only quartic, cubic,
quadratic, or linear formula.  A nonzero constant has an empty finite root
list, while the zero polynomial has the separate `identicallyZero` result.

Every finite result carries its nonzero leading coefficient as an explicit
radical as well as its roots.  The main theorem is an exact factorization,
which retains repeated roots; the root-membership characterization is then a
corollary.
-/

namespace LeanProofs.PolynomialFormulas

noncomputable section

namespace GaussianPolynomialSolver

open ExplicitRadical

/-- Coefficients of `a₄x⁴ + a₃x³ + a₂x² + a₁x + a₀`.  No leading
coefficient is required to be nonzero. -/
structure Coefficients where
  a4 : GaussianRat
  a3 : GaussianRat
  a2 : GaussianRat
  a1 : GaussianRat
  a0 : GaussianRat
deriving DecidableEq

/-- Evaluate a degree-at-most-four Gaussian-rational coefficient tuple in
`ℂ`. -/
def Coefficients.eval (c : Coefficients) (x : ℂ) : ℂ :=
  quartic (GaussianRat.toComplex c.a4) (GaussianRat.toComplex c.a3)
    (GaussianRat.toComplex c.a2) (GaussianRat.toComplex c.a1)
    (GaussianRat.toComplex c.a0) x

/-- A finite, multiplicity-preserving radical factorization. -/
structure FiniteRoots where
  leading : ExplicitRadical
  leading_ne_zero : leading.value ≠ 0
  roots : List ExplicitRadical

/-- The zero polynomial vanishes at every complex number; every other input
has a finite root list. -/
inductive RootDescription where
  | identicallyZero
  | finite (data : FiniteRoots)

namespace RootDescription

/-- The value of the factorization represented by a solver result. -/
def productValue : RootDescription → ℂ → ℂ
  | .identicallyZero, _ => 0
  | .finite data, x =>
      data.leading.value * (data.roots.map fun r => x - r.value).prod

/-- Membership in the mathematical solution set represented by a result. -/
def Contains : RootDescription → ℂ → Prop
  | .identicallyZero, _ => True
  | .finite data, x => ∃ r ∈ data.roots, r.value = x

/-- `none` means every complex number is a root; `some n` records the finite
root-list length, including multiplicity. -/
def rootCount : RootDescription → Option ℕ
  | .identicallyZero => none
  | .finite data => some data.roots.length

end RootDescription

/-- The explicit root `-b/a` of a genuine Gaussian-rational linear
polynomial. -/
def linearRoot (a b : GaussianRat) : ExplicitRadical :=
  -ofGaussian b / ofGaussian a

@[simp]
theorem linearRoot_value (a b : GaussianRat) :
    (linearRoot a b).value =
      solveLinear (GaussianRat.toComplex a) (GaussianRat.toComplex b) := by
  simp [linearRoot, solveLinear]

/-- Exact factorization of a genuine linear polynomial by its explicit
radical root. -/
theorem linearRoot_factorization {a b : GaussianRat} (ha : a ≠ 0) (x : ℂ) :
    linear (GaussianRat.toComplex a) (GaussianRat.toComplex b) x =
      GaussianRat.toComplex a * (x - (linearRoot a b).value) := by
  rw [linearRoot_value]
  unfold linear solveLinear
  field_simp [GaussianRat.toComplex_ne_zero_of_ne_zero ha]
  ring

/-- Total coefficient-only radical solver through degree four.

All case tests are decidable equalities of Gaussian rationals.  Radical
selection itself is noncomputable because `RadicalExpression.nthRoot` stores
an actual chosen complex value and its proved power equation. -/
def solve (c : Coefficients) : RootDescription :=
  if h4 : c.a4 ≠ 0 then
    .finite
      { leading := ofGaussian c.a4
        leading_ne_zero := by
          simpa using GaussianRat.toComplex_ne_zero_of_ne_zero h4
        roots :=
          [ GaussianQuarticSolver.quarticRoots c.a4 c.a3 c.a2 c.a1 c.a0 h4 0
          , GaussianQuarticSolver.quarticRoots c.a4 c.a3 c.a2 c.a1 c.a0 h4 1
          , GaussianQuarticSolver.quarticRoots c.a4 c.a3 c.a2 c.a1 c.a0 h4 2
          , GaussianQuarticSolver.quarticRoots c.a4 c.a3 c.a2 c.a1 c.a0 h4 3 ] }
  else if h3 : c.a3 ≠ 0 then
    .finite
      { leading := ofGaussian c.a3
        leading_ne_zero := by
          simpa using GaussianRat.toComplex_ne_zero_of_ne_zero h3
        roots :=
          [ GaussianCubicSolver.cubicRoots c.a3 c.a2 c.a1 c.a0 0
          , GaussianCubicSolver.cubicRoots c.a3 c.a2 c.a1 c.a0 1
          , GaussianCubicSolver.cubicRoots c.a3 c.a2 c.a1 c.a0 2 ] }
  else if h2 : c.a2 ≠ 0 then
    .finite
      { leading := ofGaussian c.a2
        leading_ne_zero := by
          simpa using GaussianRat.toComplex_ne_zero_of_ne_zero h2
        roots :=
          [ GaussianCubicSolver.quadraticRoots c.a2 c.a1 c.a0 0
          , GaussianCubicSolver.quadraticRoots c.a2 c.a1 c.a0 1 ] }
  else if h1 : c.a1 ≠ 0 then
    .finite
      { leading := ofGaussian c.a1
        leading_ne_zero := by
          simpa using GaussianRat.toComplex_ne_zero_of_ne_zero h1
        roots := [linearRoot c.a1 c.a0] }
  else if h0 : c.a0 ≠ 0 then
    .finite
      { leading := ofGaussian c.a0
        leading_ne_zero := by
          simpa using GaussianRat.toComplex_ne_zero_of_ne_zero h0
        roots := [] }
  else
    .identicallyZero

/-- The solver output is an exact product factorization.  Consequently the
list records roots with multiplicity, not merely the underlying root set. -/
theorem solve_factorization (c : Coefficients) (x : ℂ) :
    c.eval x = (solve c).productValue x := by
  classical
  unfold solve
  split
  next h4 =>
    simp only [RootDescription.productValue, List.map_cons, List.map_nil,
      List.prod_cons, List.prod_nil, value_ofGaussian, mul_one]
    simpa [Coefficients.eval, mul_assoc] using
      GaussianQuarticSolver.quarticRoots_factorization
        (a := c.a4) (b := c.a3) (c := c.a2) (d := c.a1) (e := c.a0) h4 x
  next h4 =>
    have ha4 : c.a4 = 0 := not_ne_iff.mp h4
    split
    next h3 =>
      simp only [RootDescription.productValue, List.map_cons, List.map_nil,
        List.prod_cons, List.prod_nil, value_ofGaussian, mul_one]
      simpa [Coefficients.eval, quartic, cubic, ha4, mul_assoc] using
        GaussianCubicSolver.cubicRoots_factorization
          (a := c.a3) (b := c.a2) (c := c.a1) (d := c.a0) h3 x
    next h3 =>
      have ha3 : c.a3 = 0 := not_ne_iff.mp h3
      split
      next h2 =>
        simp only [RootDescription.productValue, List.map_cons, List.map_nil,
          List.prod_cons, List.prod_nil, value_ofGaussian, mul_one]
        simpa [Coefficients.eval, quartic, quadratic, ha4, ha3, mul_assoc] using
          GaussianCubicSolver.quadraticRoots_factorization
            (a := c.a2) (b := c.a1) (c := c.a0) h2 x
      next h2 =>
        have ha2 : c.a2 = 0 := not_ne_iff.mp h2
        split
        next h1 =>
          simp only [RootDescription.productValue, List.map_cons, List.map_nil,
            List.prod_cons, List.prod_nil, value_ofGaussian, mul_one]
          simpa [Coefficients.eval, quartic, linear, ha4, ha3, ha2] using
            linearRoot_factorization h1 x
        next h1 =>
          have ha1 : c.a1 = 0 := not_ne_iff.mp h1
          split
          next h0 =>
            simp [RootDescription.productValue, Coefficients.eval, quartic,
              ha4, ha3, ha2, ha1]
          next h0 =>
            have ha0 : c.a0 = 0 := not_ne_iff.mp h0
            simp [RootDescription.productValue, Coefficients.eval, quartic,
              ha4, ha3, ha2, ha1, ha0]

/-- The returned description contains exactly all complex roots. -/
theorem eval_eq_zero_iff_contains (c : Coefficients) (x : ℂ) :
    c.eval x = 0 ↔ (solve c).Contains x := by
  rw [solve_factorization]
  cases h : solve c with
  | identicallyZero => simp [RootDescription.productValue, RootDescription.Contains]
  | finite data =>
      simp only [RootDescription.productValue, RootDescription.Contains]
      rw [mul_eq_zero]
      simp only [data.leading_ne_zero, false_or, List.prod_eq_zero_iff,
        List.mem_map]
      constructor
      · rintro ⟨r, hr, hx⟩
        exact ⟨r, hr, (sub_eq_zero.mp hx).symm⟩
      · rintro ⟨r, hr, rfl⟩
        exact ⟨r, hr, sub_self r.value⟩

/-- The solver reports exactly four, three, two, one, or zero finite roots
according to the first nonzero coefficient, and `none` only for the zero
polynomial. -/
theorem solve_rootCount (c : Coefficients) :
    (solve c).rootCount =
      if c.a4 ≠ 0 then some 4
      else if c.a3 ≠ 0 then some 3
      else if c.a2 ≠ 0 then some 2
      else if c.a1 ≠ 0 then some 1
      else if c.a0 ≠ 0 then some 0
      else none := by
  classical
  by_cases h4 : c.a4 ≠ 0
  · simp [solve, RootDescription.rootCount, h4]
  · by_cases h3 : c.a3 ≠ 0
    · simp [solve, RootDescription.rootCount, h4, h3]
    · by_cases h2 : c.a2 ≠ 0
      · simp [solve, RootDescription.rootCount, h4, h3, h2]
      · by_cases h1 : c.a1 ≠ 0
        · simp [solve, RootDescription.rootCount, h4, h3, h2, h1]
        · by_cases h0 : c.a0 ≠ 0
          · simp [solve, RootDescription.rootCount, h4, h3, h2, h1, h0]
          · simp [solve, RootDescription.rootCount, h4, h3, h2, h1, h0]

end GaussianPolynomialSolver

end

end LeanProofs.PolynomialFormulas
