import DiophantineConsistency.HerbrandContextualTreeSelection
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandContextualTreeSelectionChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate PRAHerbrandSelection
  HerbrandParameterizedWitness HerbrandUniversalTree HerbrandContextualTreeSelection
example {n : ℕ} (side : Semisentence language n) (φ : Semisentence language (n+1))
    (hφ : φ.Open) (hside : ExistentialTree (parameterSide side))
    (p : UniversalAxiom ⊢ ((parameterSide side) ⋎ (∃⁰ (parameterMatrix φ))).univCl) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* (side ⋎ openMatrixAt φ c)) :=
  PRA_exists_existentialSideSelection side φ hφ hside p
#print axioms down
#print axioms neg_tree
#print axioms PRA_exists_existentialSideSelection
end DiophantineConsistency.HerbrandContextualTreeSelectionChecks
