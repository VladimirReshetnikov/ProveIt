import DiophantineConsistency.PRAHerbrandSelection

open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRAUniversalCandidate
  DiophantineConsistency.PRAHerbrandSelection

example {n : ℕ} (φ : Semisentence language (n+1)) (hφ : φ.Open)
    (fallback : Code n) (ws : List (Code n))
    (h : UniversalAxiom ⊢ (∀⁰* openMatrixList φ fallback ws)) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* openMatrixAt φ c) :=
  PRA_exists_witness_of_openDisjunction φ hφ fallback ws h
#print axioms DiophantineConsistency.PRAHerbrandSelection.modelMatrixAt
#print axioms DiophantineConsistency.PRAHerbrandSelection.PRA_exists_witness_of_openDisjunction
#check DiophantineConsistency.PRAHerbrandSelection.PRA_exists_witness_of_openDisjunction
