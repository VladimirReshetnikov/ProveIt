import DiophantineConsistency.HerbrandContextualWitness
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandContextualWitnessChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandContextualWitness
example (side : Proposition language) (hs : UniversalPrefix side)
    (θ : Semiproposition language 1) (ht : θ.Open)
    (p : UniversalAxiom ⊢ ((∼side) ⋎ (∃⁰ θ)).univCl) :
    ∃ n, UniversalAxiom ⊢ ((∼side) ⋎ termOutput θ (List.range n)).univCl :=
  universal_proves_contextual side hs θ ht p
#print axioms no_contextual_countermodel
#print axioms universal_proves_contextual
end DiophantineConsistency.HerbrandContextualWitnessChecks
