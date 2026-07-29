import PolynomialFormulas.Quartic

/-!
# Exact solver examples

These examples reduce the solver functions on equations whose radical data are
rational, demonstrating the computational interface independently of the
generic correctness theorems.
-/

namespace LeanProofs.PolynomialFormulas

example : solveLinear (2 : ℚ) 4 = -2 := by
  norm_num [solveLinear]

example : solveQuadratic (1 : ℚ) (-5) 6 1 0 = 3 := by
  norm_num [solveQuadratic]

example : solveQuadratic (1 : ℚ) (-5) 6 1 1 = 2 := by
  norm_num [solveQuadratic]

example : ∀ i, solveCubic (1 : ℚ) 0 0 (-1) 1 0 1 i = 1 := by
  intro i
  fin_cases i <;> norm_num [solveCubic]

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

end LeanProofs.PolynomialFormulas
