import DiophantineConsistency.PRAFiniteWitnessChoice

/-! Collapse a finite Herbrand-style witness disjunction to one PR witness. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAFiniteWitnessList
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRABooleanOps PRACharacteristicBit
  PRAFiniteWitnessChoice

def chooseList {n : ℕ} (good : Code (n+1)) (fallback : Code n) : List (Code n) → Code n
  | [] => fallback
  | w :: ws => chooseWitness good w (chooseList good fallback ws)

def witnessFormula {n : ℕ} (good : Code (n+1)) (w : Code n) : Semisentence language n :=
  Semiformula.rel Language.ORing.Rel.eq
    ![applyCode (applyWitness good w) (vars n), applyCode oneCode Fin.elim0]

def listFormula {n : ℕ} (good : Code (n+1)) (fallback : Code n) : List (Code n) → Semisentence language n
  | [] => witnessFormula good fallback
  | w :: ws => witnessFormula good w ⋎ listFormula good fallback ws

def listSentence {n : ℕ} (good : Code (n+1)) (fallback : Code n) (ws : List (Code n)) : Sentence language :=
  ∀⁰* listFormula good fallback ws

def listSelectedSentence {n : ℕ} (good : Code (n+1)) (fallback : Code n) (ws : List (Code n)) : Sentence language :=
  ∀⁰* witnessFormula good (chooseList good fallback ws)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

omit [M↓[language] ⊧* PRA] in
theorem modelWitnessFormula {n : ℕ} (good : Code (n+1)) (w : Code n) (e : Fin n → M) :
    (witnessFormula good w).Eval e Empty.elim ↔
      Structure.func (L := language) (applyWitness good w) e =
        Structure.func (L := language) oneCode Fin.elim0 := by
  simp [witnessFormula, Semiformula.eval_rel, eqRel, applyCode, vars, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]

/-- Pointwise selector correctness in arbitrary models, with the predicate's
0/1 range supplied for all witness values. -/
theorem modelChooseList {n : ℕ} (good : Code (n+1)) (fallback : Code n) (ws : List (Code n))
    (e : Fin n → M) (hBit : M↓[language] ⊧ bitSentence good)
    (hEither : (listFormula good fallback ws).Eval e Empty.elim) :
    (witnessFormula good (chooseList good fallback ws)).Eval e Empty.elim := by
  induction ws with
  | nil => exact hEither
  | cons w ws ih =>
      have hcases : (witnessFormula good w).Eval e Empty.elim ∨
          (listFormula good fallback ws).Eval e Empty.elim := by simpa [listFormula] using hEither
      apply (modelWitnessFormula good _ e).mpr
      apply modelChooseWitness good w (chooseList good fallback ws) e
      · rw [modelApplyWitness]
        exact modelBitSentence good hBit _
      · rcases hcases with hw | hw
        · exact Or.inl ((modelWitnessFormula good w e).mp hw)
        · exact Or.inr ((modelWitnessFormula good _ e).mp (ih hw))

theorem modelListSelectedSentence {n : ℕ} (good : Code (n+1)) (fallback : Code n)
    (ws : List (Code n)) (hBit : M↓[language] ⊧ bitSentence good)
    (hEither : M↓[language] ⊧ listSentence good fallback ws) :
    M↓[language] ⊧ listSelectedSentence good fallback ws := by
  simp only [models_iff, listSentence, Semiformula.eval_allClosure] at hEither
  simp only [models_iff, listSelectedSentence, Semiformula.eval_allClosure]
  intro e
  exact modelChooseList good fallback ws e hBit (hEither e)

end models

/-- A provable finite disjunction of candidate witness terms can be collapsed
to one fixed primitive-recursive witness, provided the predicate is provably
Boolean-valued. This does not extract the disjunction from a Π₂ proof. -/
theorem PRA_proves_listWitnessChoice {n : ℕ} (good : Code (n+1)) (fallback : Code n)
    (ws : List (Code n)) (hBit : PRA ⊢ bitSentence good)
    (hEither : PRA ⊢ listSentence good fallback ws) :
    PRA ⊢ listSelectedSentence good fallback ws := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  apply modelListSelectedSentence
  · exact models_of_provable (inferInstance : M↓[language] ⊧* PRA) hBit
  · exact models_of_provable (inferInstance : M↓[language] ⊧* PRA) hEither

end DiophantineConsistency.PRAFiniteWitnessList
