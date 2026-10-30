import DiophantineConsistency.HerbrandContextualTreeSelection
import DiophantineConsistency.HerbrandExistentialTreeRew
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandExistentialSideSelection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalCandidate PRAHerbrandSelection
  HerbrandParameterizedWitness HerbrandUniversalTree HerbrandContextualTreeSelection HerbrandExistentialTreeRew

/-- Contextual selection for an unrewritten existential side tree, preserving
all of its parameters. -/
theorem PRA_exists_selected {n : ℕ} (side : Semisentence language n)
    (φ : Semisentence language (n+1)) (hφ : φ.Open)
    (hside : ExistentialTree side)
    (p : UniversalAxiom ⊢ ((parameterSide side) ⋎ (∃⁰ (parameterMatrix φ))).univCl) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* (side ⋎ openMatrixAt φ c)) := by
  apply PRA_exists_existentialSideSelection side φ hφ
  · exact existential_rew hside _
  · exact p
end DiophantineConsistency.HerbrandExistentialSideSelection
