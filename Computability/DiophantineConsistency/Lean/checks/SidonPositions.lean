import DiophantineConsistency.SidonPositions

open DiophantineConsistency.SidonPositions

/-- The zero-dimensional case still has its constant position. -/
example : weight 0 0 = 0 := by decide

/-- The first nontrivial position list is literal executable arithmetic. -/
example : [weight 2 0, weight 2 1, weight 2 2] = [0, 10, 22] := by decide

/-- In particular, repeated-index pair sums remain distinct. -/
example : weight 2 1 + weight 2 1 ≠ weight 2 0 + weight 2 2 := by decide

/-- Constant and linear monomials use the same canonical pair API. -/
example : pairWeight (orderedPair (0 : Fin 3) 2) = 22 := by decide
example : pairWeight (orderedPair (2 : Fin 3) 0) = 22 := by decide

/-- Exhaustive small-instance regression of the unordered-pair statement. -/
example : ∀ i j k l : Fin 3,
    weight 2 i + weight 2 j = weight 2 k + weight 2 l ↔
      (i = k ∧ j = l) ∨ (i = l ∧ j = k) := by decide

example : weight 3 (Fin.last 3) = 66 := by decide
example (i : Fin 4) : weight 3 i ≤ 108 := weight_le_four_cube (by decide) i

#print axioms weight_sum_eq_iff
#print axioms pairWeight_injective
#print axioms weight_le_cubic
