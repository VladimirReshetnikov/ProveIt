import DiophantineConsistency.RatioReparameterization

open DiophantineConsistency.RatioReparameterization

-- Nontrivial exact forward and reverse quotient formulas.
example : newIndex 1 3 7 10 = 0 := by decide
example : oldIndex 1 3 7 0 = 3 := by decide
example : newIndex 1 3 7 52 = 2 := by decide
example : oldIndex 1 3 7 2 = 17 := by decide
example : newH 1 3 7 2 = oldH 1 3 17 := by decide

example : (2 : ℤ) ∣ 2 ∧ (52 : ℤ) = newH 1 3 7 (newIndex 1 3 7 52) :=
  newIndex_correct (j := 17) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)

-- F=1 is included and preserves the boundary new index zero.
example : 1 ≤ oldIndex 1 3 1 0 ∧ newH 1 3 1 0 = oldH 1 3 (oldIndex 1 3 1 0) :=
  oldIndex_correct (by decide) (by decide) (by decide) (by decide) 0

-- The coprimality congruence cannot be omitted from combined divisibility.
example : (2 : ℤ) * 2 ∣ 1 * 2 + 2 * (4 - 3) := by decide
example : ¬ (2 : ℤ) ∣ 1 := by decide

-- Without C | F-1, the new nonnegative index need not preserve old H.
example : (1 : ℤ) * 2 ∣ 1 * 2 + 1 * (7 - 3) := by decide
example : newH 1 3 2 (newIndex 1 3 2 7) ≠ 7 := by decide

-- The positive old-index requirement is essential.
example : newH 1 3 1 (newIndex 1 3 1 (oldH 1 3 0)) ≠ oldH 1 3 0 := by decide

-- Actual polynomial recipes supply both congruences uniformly.
example : (5 : ℤ) ∣ F 2 1 5 3 7 - 1 ∧ (3 : ℤ) ∣ F 2 1 5 3 7 - 1 :=
  F_congruences 2 1 5 3 7

#print axioms newIndex
#print axioms oldIndex
#print axioms newIndex_correct
#print axioms oldIndex_correct
#print axioms exists_old_iff_new
#print axioms F_congruences
#print axioms vars_F_congruences
