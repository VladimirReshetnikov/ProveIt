import DiophantineConsistency.HerbrandInteractiveTriple
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandInteractiveTripleChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandSchedule HerbrandInteractiveTriple
example (ψ : Semiproposition language 4) (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (∼ψ))))).univCl) :
    ∃ n, (UniversalAxiom ⊢ (output ψ.fvSup ψ (List.range n)).univCl) ∧
      (∀ j i, (candidate j).FVar? i → i < ψ.fvSup+3*j) ∧
      (∀ j i, (bad ψ.fvSup j ψ).FVar? i → i ≤ ψ.fvSup+3*j+2) :=
  separated_interactive ψ hψ p
#print axioms HerbrandGeneratedSubmodelTriple.no_triple_countermodel
#print axioms separated_interactive
end DiophantineConsistency.HerbrandInteractiveTripleChecks
