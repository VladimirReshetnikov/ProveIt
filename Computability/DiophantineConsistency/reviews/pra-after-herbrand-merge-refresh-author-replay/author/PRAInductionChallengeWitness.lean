import DiophantineConsistency.HerbrandTripleWitness
import DiophantineConsistency.HerbrandPackedTriple
/-! Three coordinated PR challenges defeating a coded induction counterexample. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAInductionChallengeWitness
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAFiniteTripleChoice
  PRAInductionCounterexample HerbrandPackedTriple HerbrandTripleWitness PRAHerbrandTripleSelection

/-- Each fixed coded induction counterexample admits three PR challenge
functions, and candidate PRA proves their joint counterexample defeat. -/
theorem PRA_exists_inductionChallenges {n : ℕ} (pred : Code (n+2))
    (base stop : Code n) (q : Code (n+3)) :
    let φ := counterexampleMatrix pred base stop q
    ∃ t : Triple φ.fvSup, Primrec (eval t.first) ∧ Primrec (eval t.second) ∧
      Primrec (eval t.third) ∧ PRA ⊢ (∀⁰* matrixAt (packedTriple φ) t) := by
  apply PRA_exists_tripleWitness
  · exact packedTriple_open _ (counterexampleMatrix_open pred base stop q)
  · exact candidate_proves_packedTriple _ (PRA_proves_counterexampleSentence pred base stop q)
end DiophantineConsistency.PRAInductionChallengeWitness
