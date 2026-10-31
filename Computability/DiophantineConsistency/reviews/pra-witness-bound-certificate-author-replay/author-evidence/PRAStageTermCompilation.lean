import DiophantineConsistency.PRAStageCodedChi
import DiophantineConsistency.HerbrandFixedGoalExtraction
import DiophantineConsistency.HerbrandParameterizedWitness
/-! Compile stage candidate terms without changing their arbitrary-model values. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAStageTermCompilation
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRALanguage PRATheory PRAUniversalCandidate PRAUniversalEquivalence HerbrandParameterizedWitness
  HerbrandTupleSchedule HerbrandInteractiveFourTriple

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelParameterCode_of_support (n : ℕ) (t : SyntacticTerm language) (e : ℕ → M)
    (ht : ∀ i, t.FVar? i → i < n) :
    Structure.func (L := language) (parameterCode n t) (fun i => e i.val) = Semiterm.val ![] e t := by
  letI : M↓[language] ⊧* UniversalAxiom := by
    constructor
    intro σ hσ
    exact models_of_provable (inferInstance : M↓[language] ⊧* PRA) (PRA_proves_universalAxiom hσ)
  rw [modelParameterCode]
  apply Semiterm.val_eq_of_funEqOn
  intro i hi
  simp [parameterEnv, ht i hi]

/-- All four scheduled terms compile to codes over the current prefix without
changing their interpretation under the original arbitrary valuation. -/
theorem modelCandidateCode (r j : ℕ) (k : Fin 4) (e : ℕ → M) :
    Structure.func (L := language) (parameterCode (r+3*j) (candidate j k))
      (fun i => e i.val) = Semiterm.val ![] e (candidate j k) := by
  apply modelParameterCode_of_support
  intro i hi
  exact term_support r j k hi
end models
end DiophantineConsistency.PRAStageTermCompilation
