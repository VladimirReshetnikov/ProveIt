import DiophantineConsistency.GapSourceExistence66

open DiophantineConsistency GapSourceExistence66

-- The public tuple has j_plus; the arithmetic CRT index itself is natural.
example (x : Fin 9 → ℕ) : (positiveVars (fun i => x i+1)).j=x 7 := rfl
example (x : Fin 9 → ℕ) : (naturalVars x).j=x 7 := rfl

#print axioms hasZero_iff_source
#print axioms exists_positive_zero_iff_hasZero
#print axioms positiveValue_successors
#print axioms exists_natural_zero_iff_hasZero
#print axioms exists_natural_zero_iff_source
#print axioms no_natural_zero_iff
