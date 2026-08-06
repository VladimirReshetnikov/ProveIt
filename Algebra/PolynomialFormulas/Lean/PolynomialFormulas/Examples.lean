import PolynomialFormulas.GaussianRadicalBounds
import PolynomialFormulas.GaussianPolynomialApproximation
import PolynomialFormulas.GaussianQuinticSolver
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Exact solver examples

These examples reduce the solver functions on equations whose radical data are
rational, demonstrating the computational interface independently of the
generic correctness theorems.
-/

namespace LeanProofs.PolynomialFormulas

noncomputable def complexPrimitiveCubeRoot : ℂ := Complex.exp (2 * Real.pi * Complex.I / 3)

theorem complexPrimitiveCubeRoot_spec :
    complexPrimitiveCubeRoot ^ 2 + complexPrimitiveCubeRoot + 1 = 0 := by
  have hprimitive : IsPrimitiveRoot complexPrimitiveCubeRoot 3 := by
    exact Complex.isPrimitiveRoot_exp 3 (by norm_num)
  have hsum := hprimitive.geom_sum_eq_zero (by norm_num : 1 < 3)
  norm_num [Finset.sum_range_succ] at hsum
  linear_combination hsum

example : solveLinear (2 : ℚ) 4 = -2 := by
  norm_num [solveLinear]

example : solveQuadratic (1 : ℚ) (-5) 6 1 0 = 3 := by
  norm_num [solveQuadratic]

example : solveQuadratic (1 : ℚ) (-5) 6 1 1 = 2 := by
  norm_num [solveQuadratic]

example : ∀ i, solveCubic (1 : ℚ) 0 0 (-1) 1 0 1 i = 1 := by
  intro i
  fin_cases i <;> norm_num [solveCubic]

/-- Cardano's complex collection for `x³ - 1` contains every root. -/
example (x : ℂ) :
    cubic 1 0 0 (-1) x = 0 ↔
      ∃ i, solveCubic 1 0 0 (-1) 1 0 complexPrimitiveCubeRoot i = x := by
  apply cubic_eq_zero_iff (s := (1 / 2 : ℂ)) (ha := by norm_num)
  · norm_num [cubicP, cubicQ, cubicDelta]
  · norm_num [cubicQ]
  · norm_num [cubicQ]
  · norm_num [cubicP]
  · exact complexPrimitiveCubeRoot_spec

example : solveQuartic (1 : ℚ) 0 (-5) 0 4 2 3 0 1 1 0 = 2 := by
  norm_num [solveQuartic, solveDepressedQuartic]

example : solveQuartic (1 : ℚ) 0 (-5) 0 4 2 3 0 1 1 1 = 1 := by
  norm_num [solveQuartic, solveDepressedQuartic]

example : solveQuartic (1 : ℚ) 0 (-5) 0 4 2 3 0 1 1 2 = -1 := by
  simp [solveQuartic, solveDepressedQuartic]
  norm_num

example : solveQuartic (1 : ℚ) 0 (-5) 0 4 2 3 0 1 1 3 = -2 := by
  simp [solveQuartic, solveDepressedQuartic]
  norm_num

/-- The four exact values above come with one uniform correctness proof. -/
example (i : Fin 4) :
    quartic (1 : ℚ) 0 (-5) 0 4
      (solveQuartic 1 0 (-5) 0 4 2 3 0 1 1 i) = 0 := by
  apply solveQuartic_correct (ha := by norm_num)
  all_goals norm_num [quarticP, quarticQ, quarticR]

/-- The displayed quartic list also contains every rational root. -/
example (x : ℚ) :
    quartic 1 0 (-5) 0 4 x = 0 ↔
      ∃ i, solveQuartic 1 0 (-5) 0 4 2 3 0 1 1 i = x := by
  apply quartic_eq_zero_iff (ha := by norm_num)
  all_goals norm_num [quarticP, quarticQ, quarticR]

/-! The total Gaussian-rational solver chooses all required radicals itself. -/

open GaussianPolynomialSolver

/-- Zero quartic and cubic coefficients dispatch to the quadratic solver. -/
example :
    (solve
      { a4 := 0
        a3 := 0
        a2 := 1
        a1 := 0
        a0 := -1 }).rootCount = some 2 := by
  rw [solve_rootCount]
  norm_num

/-- Gaussian, rather than merely rational, coefficients are accepted.  This
is `(x - I)² = x² - 2Ix - 1`; the theorem states that the returned explicit
radical list contains exactly all its complex roots. -/
example (x : ℂ) :
    let c : Coefficients :=
      { a4 := 0
        a3 := 0
        a2 := 1
        a1 := ⟨0, -2⟩
        a0 := -1 }
    c.eval x = 0 ↔ (solve c).Contains x := by
  intro c
  exact eval_eq_zero_iff_contains c x

/-! The quintic dispatcher literally reuses that solver when `a₅ = 0`. -/

/-- A nominal quintic with zero leading coefficient dispatches to the same
quadratic result as above. -/
example :
    let c : GaussianQuinticSolver.Coefficients :=
      { a5 := 0
        a4 := 0
        a3 := 0
        a2 := 1
        a1 := 0
        a0 := -1 }
    (GaussianQuinticSolver.solve c).rootCount = some 2 := by
  intro c
  rw [GaussianQuinticSolver.solve_of_a5_eq_zero c rfl]
  change (GaussianPolynomialSolver.solve c.toQuartic).rootCount = some 2
  rw [GaussianPolynomialSolver.solve_rootCount]
  norm_num [c, GaussianQuinticSolver.Coefficients.toQuartic]

/-- The complete-radical fallback contract ensures that the singular but
solvable genuine quintic `x⁵` is not mistaken for an unsupported input. -/
example :
    let c : GaussianQuinticSolver.Coefficients :=
      { a5 := 1
        a4 := 0
        a3 := 0
        a2 := 0
        a1 := 0
        a0 := 0 }
    (GaussianQuinticSolver.solve c).rootCount = some 5 := by
  intro c
  apply
    GaussianQuinticSolver.solve_rootCount_of_a5_ne_zero_of_completeRadicalSolution
      c (by norm_num [c])
  exact ⟨{
    roots := fun _ => 0
    factorization := by
      intro x
      simp [c, GaussianQuinticSolver.Coefficients.eval,
        GaussianQuinticSolver.Coefficients.toQuartic,
        GaussianPolynomialSolver.Coefficients.eval, quartic] }⟩

/-- The all-zero tuple is represented separately because every complex value
is then a root. -/
example (x : ℂ) :
    let c : Coefficients :=
      { a4 := 0, a3 := 0, a2 := 0, a1 := 0, a0 := 0 }
    (solve c).Contains x := by
  simp [solve, RootDescription.Contains]

/-! Every proof-carrying radical value also has an arbitrarily small certified
rational rectangle. -/

example (r : ExplicitRadical) (ε : ℚ) (hε : 0 < ε) :
    (r.boundingBox ε hε).IsEnclosure r.value ε :=
  r.boundingBox_spec ε hε

example (c : Coefficients) (data : FiniteRoots)
    (hsolve : solve c = .finite data) (r : ExplicitRadical)
    (hr : r ∈ data.roots) :
    c.eval r.value = 0 ∧
      (r.boundingBox (1 / 100) (by norm_num)).IsEnclosure r.value (1 / 100) :=
  returnedRoot_boundingBox_spec c data hsolve r hr (1 / 100) (by norm_num)

/-! The separate certificate-search API returns literal, executable Gaussian
rationals and does not evaluate the theorem-side chosen radical values. -/

namespace ExecutableApproximationExample

open GaussianPolynomialApproximationNormalization
open GaussianPolynomialApproximation

private def linearCoefficients : Coefficients where
  a4 := 0
  a3 := 0
  a2 := 0
  a1 := 1
  a0 := -2

private theorem linearCoefficients_nonzero : Nonzero linearCoefficients := by
  unfold Nonzero
  native_decide

/-- The leading-zero input `x - 2` executes to the one-entry vector `[2]`. -/
example :
    (approximations linearCoefficients 1 linearCoefficients_nonzero
      (by norm_num)).toList = [(2 : GaussianRat)] := by
  native_decide

/-- The general theorem supplies a position-matched list of all exact complex
roots and the Manhattan error bound. -/
example := approximations_correct linearCoefficients 1
  linearCoefficients_nonzero (by norm_num)

end ExecutableApproximationExample

end LeanProofs.PolynomialFormulas
