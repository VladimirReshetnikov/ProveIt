import DiophantineConsistency.HerbrandContextualSelection
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandContextualSelectionChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalSyntax PRAUniversalCandidate
  PRAHerbrandSelection HerbrandParameterizedWitness HerbrandContextualSelection
example {n : ℕ} (side : Semisentence language n) (φ : Semisentence language (n+1))
    (hφ : φ.Open) (hside : UniversalPrefix (∼(parameterSide side)))
    (p : UniversalAxiom ⊢ ((parameterSide side) ⋎ (∃⁰ (parameterMatrix φ))).univCl) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* (side ⋎ openMatrixAt φ c)) :=
  PRA_exists_contextualSelection side φ hφ hside p
#print axioms modelParameterSide
#print axioms PRA_exists_contextualSelection
end DiophantineConsistency.HerbrandContextualSelectionChecks
