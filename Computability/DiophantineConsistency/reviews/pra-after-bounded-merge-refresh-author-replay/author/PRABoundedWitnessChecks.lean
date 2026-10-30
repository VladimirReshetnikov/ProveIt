import DiophantineConsistency.PRABoundedWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.PRAFiniteFunctionCodes DiophantineConsistency.PRALanguage
  DiophantineConsistency.PRATheory DiophantineConsistency.PRAHerbrandSelection
  DiophantineConsistency.PRABoundedWitness
#print axioms characteristicMatrix_open
#print axioms PRA_boundedWitness
#check PRA_boundedWitness
example (φ : Semisentence language 1) (hφ : Hierarchy 𝚺 0 φ) (h : PRA ⊢ ∃⁰ φ) :
    ∃ w : Code 0, Primrec (eval w) ∧ PRA ⊢ (∀⁰* openMatrixAt φ w) :=
  PRA_boundedWitness φ hφ (by simpa using h)
