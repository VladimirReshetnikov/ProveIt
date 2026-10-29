import DiophantineConsistency.PRAHerbrandSelection
/-! Preserve an arbitrary side formula while selecting a finite PR witness. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAContextualWitnessChoice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAEqualityCode PRAOpenFormulaCompiler
  PRACharacteristicBit PRAFiniteWitnessChoice PRAFiniteWitnessList PRAHerbrandSelection

theorem PRA_proves_contextualListChoice {n : ℕ} (side : Semisentence language n)
    (good : Code (n+1)) (fallback : Code n) (ws : List (Code n))
    (hBit : PRA ⊢ bitSentence good)
    (h : PRA ⊢ (∀⁰* (side ⋎ listFormula good fallback ws))) :
    PRA ⊢ (∀⁰* (side ⋎ witnessFormula good (chooseList good fallback ws))) := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hb := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hBit
  have hh := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
  simp only [models_iff, Semiformula.eval_allClosure] at hh ⊢
  intro e
  have hc : side.Eval e Empty.elim ∨ (listFormula good fallback ws).Eval e Empty.elim := by
    simpa using hh e
  change side.Eval e Empty.elim ∨ (witnessFormula good (chooseList good fallback ws)).Eval e Empty.elim
  rcases hc with hs | hw
  · exact Or.inl hs
  · exact Or.inr (modelChooseList good fallback ws e hb hw)

/-- A finite open-matrix disjunction can be collapsed while preserving any
side formula, including one containing existential quantifiers. -/
theorem PRA_exists_contextualWitness {n : ℕ} (side : Semisentence language n)
    (φ : Semisentence language (n+1)) (hOpen : φ.Open) (fallback : Code n) (ws : List (Code n))
    (h : PRA ⊢ (∀⁰* (side ⋎ openMatrixList φ fallback ws))) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ (∀⁰* (side ⋎ openMatrixAt φ c)) := by
  obtain ⟨p, _, hp⟩ := PRAOpenFormulaCoverage.parseFormula_open φ hOpen
  subst φ
  have hcoded : PRA ⊢ (∀⁰* (side ⋎ listFormula (compileFormula equalityCode p) fallback ws)) := by
    apply Theory.Proof.complete_on_eq_models.{0,0}
    intro M _ _ _ _
    have hh := models_of_provable (inferInstance : M↓[language] ⊧* PRA) h
    simp only [models_iff, Semiformula.eval_allClosure] at hh ⊢
    intro e
    have hc : side.Eval e Empty.elim ∨ (openMatrixList (asFormula p) fallback ws).Eval e Empty.elim := by
      simpa using hh e
    change side.Eval e Empty.elim ∨ (listFormula (compileFormula equalityCode p) fallback ws).Eval e Empty.elim
    rcases hc with hs | hw
    · exact Or.inl hs
    · rw [openMatrixList_asFormula] at hw
      exact Or.inr ((modelMatrixList p fallback ws e).mp hw)
  let c := chooseList (compileFormula equalityCode p) fallback ws
  have hsel := PRA_proves_contextualListChoice side (compileFormula equalityCode p) fallback ws
    (PRA_proves_compiledBit p) hcoded
  refine ⟨c, eval_primrec _, ?_⟩
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hh := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hsel
  simp only [models_iff, Semiformula.eval_allClosure] at hh ⊢
  intro e
  have hc : side.Eval e Empty.elim ∨ (witnessFormula (compileFormula equalityCode p) c).Eval e Empty.elim := by
    simpa [c] using hh e
  change side.Eval e Empty.elim ∨ (openMatrixAt (asFormula p) c).Eval e Empty.elim
  rcases hc with hs | hw
  · exact Or.inl hs
  · exact Or.inr ((modelMatrixAt p c e).mpr hw)
end DiophantineConsistency.PRAContextualWitnessChoice
