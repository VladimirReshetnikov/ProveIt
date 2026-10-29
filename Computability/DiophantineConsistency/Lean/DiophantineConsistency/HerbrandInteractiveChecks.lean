import DiophantineConsistency.HerbrandInteractive
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandInteractiveChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalSyntax PRAUniversalCandidate HerbrandSchedule HerbrandInteractive

example (t : SyntacticTerm language) : candidate (stage t) = t := candidate_stage t
example (j i : ℕ) (h : (candidate j).FVar? i) : i < j := candidate_before j h
example (ψ : Semiproposition language 2) (hψ : UniversalPrefix ψ)
    (p : UniversalAxiom ⊢ (∃⁰ (∀⁰ (∼ψ))).univCl) :
    ∃ n, (UniversalAxiom ⊢ (output ψ.fvSup ψ (List.range n)).univCl) ∧
      (∀ j i, (candidate j).FVar? i → i < ψ.fvSup+j) ∧
      (∀ j i, (bad ψ.fvSup j ψ).FVar? i → i ≤ ψ.fvSup+j) :=
  separated_interactive ψ hψ p
#print axioms HerbrandGeneratedSubmodel.no_countermodel
#print axioms HerbrandValuationCompact.valuation_compact
#print axioms candidate_stage
#print axioms candidate_before
#print axioms separated_interactive
end DiophantineConsistency.HerbrandInteractiveChecks
