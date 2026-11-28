import Statements

/-! The five theorems of `src/Main.lean`, with `sorry` in place of their proofs, for the tool
Comparator. This file imports only `src/Statements.lean`, which imports only Mathlib. Nothing
imports this file. -/

theorem riemannHypothesis : RiemannHypothesis := by
  sorry

theorem riemannZeta_eq_zero_re : RiemannZetaZerosOnLine := by
  sorry

theorem LFunction_ne_zero_of_half_lt_re : DirichletLNonvanishingRightOfHalf := by
  sorry

theorem LFunction_eq_zero_re : DirichletLZerosOnLine := by
  sorry

theorem LFunction_eq_zero_re_of_isPrimitive : PrimitiveDirichletLZerosOnLine := by
  sorry
