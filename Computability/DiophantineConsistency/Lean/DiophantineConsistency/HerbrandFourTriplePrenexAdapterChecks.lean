import DiophantineConsistency.HerbrandFourTriplePrenexAdapter
set_option autoImplicit false
namespace DiophantineConsistency.HerbrandFourTriplePrenexAdapterChecks
open LO LO.FirstOrder
open scoped LO.FirstOrder
open PRALanguage PRAUniversalCandidate HerbrandInteractiveFourTriple HerbrandFourTriplePrenexAdapter
example (φ : Semiproposition language 8) (χ : Semiproposition language 7)
    (hφ : φ.Open) (hχ : χ.Open)
    (p : UniversalAxiom ⊢ (∃⁰ (∃⁰ (∃⁰ (∃⁰ (∀⁰ (∀⁰ (∀⁰ (sourceMatrix φ χ)))))))).univCl) :
    ∃ n, (UniversalAxiom ⊢ (output (negativePrefix φ χ).fvSup (negativePrefix φ χ) (List.range n)).univCl) ∧
      (∀ j k i, (HerbrandTupleSchedule.candidate j k).FVar? i → i < (negativePrefix φ χ).fvSup+3*j) ∧
      (∀ j i, (bad (negativePrefix φ χ).fvSup j (negativePrefix φ χ)).FVar? i →
        i ≤ (negativePrefix φ χ).fvSup+3*j+2) := extract φ χ hφ hχ p
#print axioms matrix_equiv
#print axioms normalize_proof
#print axioms extract
end DiophantineConsistency.HerbrandFourTriplePrenexAdapterChecks
