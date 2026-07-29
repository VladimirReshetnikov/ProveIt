import PolynomialFormulas.Quartic
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

end LeanProofs.PolynomialFormulas
