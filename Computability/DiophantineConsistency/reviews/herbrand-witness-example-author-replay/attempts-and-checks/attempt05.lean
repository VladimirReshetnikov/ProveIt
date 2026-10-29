import DiophantineConsistency.HerbrandAllInstantiation

set_option autoImplicit false
namespace DiophantineConsistency.HerbrandWitnessExample
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAHerbrandSelection HerbrandAllInstantiation

def equalityMatrix : Semisentence language 2 :=
  Semiformula.rel Language.ORing.Rel.eq ![.bvar 0, .bvar 1]

theorem equalityMatrix_open : equalityMatrix.Open := by simp [equalityMatrix, Semiformula.Open]

theorem equalityExists : PRA ⊢ (∀⁰* ∃⁰ equalityMatrix) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  simp only [models_iff, Semiformula.eval_allClosure]
  intro e
  refine ⟨e 0, ?_⟩
  unfold equalityMatrix
  change (Semiformula.rel Language.ORing.Rel.eq ![.bvar 0, .bvar 1] : Semisentence language 2).Eval (e 0 :> e) Empty.elim
  rw [Semiformula.eval_rel, Structure.eq_lang]
  rfl

example : ∃ c : Code 1, Primrec (eval c) ∧ PRA ⊢ (∀⁰* openMatrixAt equalityMatrix c) :=
  PRA_witness_of_exists equalityMatrix equalityMatrix_open equalityExists

end DiophantineConsistency.HerbrandWitnessExample
