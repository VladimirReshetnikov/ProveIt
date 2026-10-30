import DiophantineConsistency.HerbrandContextualWitness
import DiophantineConsistency.HerbrandContextualTreeSelection
import DiophantineConsistency.HerbrandParameterizedWitness
import DiophantineConsistency.PRAContextualWitnessChoice
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandContextualSelection
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAUniversalSyntax PRAUniversalCandidate
  PRAUniversalEquivalence PRAHerbrandSelection HerbrandSchedule HerbrandParameterizedWitness
  PRAContextualWitnessChoice

def parameterSide {n : ℕ} (side : Semisentence language n) : Proposition language :=
  Rew.embSubsts (fun i : Fin n => .fvar i.val) ▹ side

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* UniversalAxiom]

omit [Nonempty M] [Structure.Eq language M] [M↓[language] ⊧* UniversalAxiom] in
theorem modelParameterSide {n : ℕ} (side : Semisentence language n) (e : Fin n → M) :
    (parameterSide side).Eval ![] (parameterEnv n e) ↔ side.Eval e Empty.elim := by
  exact HerbrandContextualTreeSelection.modelParameterSide side e
end models

/-- Convert contextual syntactic term instances into a finite code list and
use candidate PRA's contextual selector. -/
theorem PRA_exists_contextualSelection {n : ℕ} (side : Semisentence language n)
    (φ : Semisentence language (n+1)) (hφ : φ.Open)
    (hside : UniversalPrefix (∼(parameterSide side)))
    (p : UniversalAxiom ⊢ ((parameterSide side) ⋎ (∃⁰ (parameterMatrix φ))).univCl) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* (side ⋎ openMatrixAt φ c)) := by
  exact HerbrandContextualTreeSelection.PRA_exists_contextualSelection side φ hφ
    (HerbrandUniversalTree.prefix_tree _ hside) p
end DiophantineConsistency.HerbrandContextualSelection
