import DiophantineConsistency.FirstExit
open DiophantineConsistency.FirstExit

example : ∃ k : ℕ, 0 ≤ k ∧ k ≤ 0 ∧ ¬ (k < 0) ∧
    (∀ j : ℕ, 0 ≤ j → j < k → j < 0) ∧ (k = 0 ∨ k - 1 < 0) :=
  exists_first_failure (fun j => j < 0) 0 0 (by omega) (by omega)

example : ∃ k : ℕ, 1 ≤ k ∧ k ≤ 3 ∧ ¬ (k < 3) ∧
    (∀ j : ℕ, 1 ≤ j → j < k → j < 3) ∧ (k = 1 ∨ k - 1 < 3) :=
  exists_first_failure (fun j => j < 3) 1 3 (by omega) (by omega)

#print axioms exists_first_failure
