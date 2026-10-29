import DiophantineConsistency.PRASelectCode

/-! Primitive-recursive choice between two certified witness terms. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAFiniteWitnessChoice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PRABooleanOps
  PRACharacteristicBit PRASelectCode PRANonzeroCharacter

/-- Apply a predicate code to a candidate witness and the input parameters. -/
def applyWitness {n : ℕ} (good : Code (n+1)) (candidate : Code n) : Code n :=
  .comp good (.cons candidate (pack n (fun i => .proj i)))

def chooseWitness {n : ℕ} (good : Code (n+1)) (left right : Code n) : Code n :=
  selectAmong (applyWitness good left) left right

def twoWitnessSentence {n : ℕ} (good : Code (n+1)) (left right : Code n) : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
      ![applyCode (applyWitness good left) (vars n), applyCode oneCode Fin.elim0]) ⋎
    (Semiformula.rel Language.ORing.Rel.eq
      ![applyCode (applyWitness good right) (vars n), applyCode oneCode Fin.elim0]) : Semisentence language n)

def selectedWitnessSentence {n : ℕ} (good : Code (n+1)) (left right : Code n) : Sentence language :=
  equalClosure (applyCode (applyWitness good (chooseWitness good left right)) (vars n))
    (applyCode oneCode Fin.elim0)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelApplyWitness {n : ℕ} (good : Code (n+1)) (w : Code n) (e : Fin n → M) :
    Structure.func (L := language) (applyWitness good w) e =
      Structure.func (L := language) good (Fin.cases (Structure.func (L := language) w e) e) := by
  rw [applyWitness, modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  simp only [getCode, getCode_pack]
  exact modelProjection j e

theorem modelChooseWitness {n : ℕ} (good : Code (n+1)) (left right : Code n) (e : Fin n → M)
    (hBit : IsBit (Structure.func (L := language) (applyWitness good left) e))
    (hEither : Structure.func (L := language) (applyWitness good left) e =
        Structure.func (L := language) oneCode Fin.elim0 ∨
      Structure.func (L := language) (applyWitness good right) e =
        Structure.func (L := language) oneCode Fin.elim0) :
    Structure.func (L := language) (applyWitness good (chooseWitness good left right)) e =
      Structure.func (L := language) oneCode Fin.elim0 := by
  rw [modelApplyWitness, chooseWitness, modelSelectAmong]
  rcases hBit with hz | ho
  · rw [hz, modelSelectZero]
    rcases hEither with hl | hr
    · exact False.elim ((modelOneNeZero (M := M)) (hl.symm.trans hz))
    · rw [modelApplyWitness] at hr
      exact hr
  · rw [ho, modelOneSuccZero, modelSelectSucc]
    rw [modelApplyWitness] at ho
    exact ho

theorem modelTwoWitnessSentence {n : ℕ} (good : Code (n+1)) (left right : Code n)
    (h : M↓[language] ⊧ twoWitnessSentence good left right) (e : Fin n → M) :
    Structure.func (L := language) (applyWitness good left) e =
        Structure.func (L := language) oneCode Fin.elim0 ∨
      Structure.func (L := language) (applyWitness good right) e =
        Structure.func (L := language) oneCode Fin.elim0 := by
  simp only [models_iff, twoWitnessSentence, Semiformula.eval_allClosure] at h
  have h := h e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _ at h
  simp [Semiformula.EvalAux, eqRel, applyCode, vars, Function.comp_def] at h
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz] at h
  exact h

theorem modelBitSentence {n : ℕ} (good : Code (n+1))
    (h : M↓[language] ⊧ bitSentence good) (e : Fin (n+1) → M) :
    IsBit (Structure.func (L := language) good e) := by
  simp only [models_iff, bitSentence, Semiformula.eval_allClosure] at h
  have h := h e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _ at h
  simp [Semiformula.EvalAux, eqRel, applyCode, vars, Function.comp_def] at h
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN (n+1))) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz] at h
  exact h

theorem modelSelectedSentence {n : ℕ} (good : Code (n+1)) (left right : Code n)
    (hBit : M↓[language] ⊧ bitSentence good)
    (hEither : M↓[language] ⊧ twoWitnessSentence good left right) :
    M↓[language] ⊧ selectedWitnessSentence good left right := by
  apply (eqClosureModels _ _).mpr
  intro e
  simp only [applyCode, Semiterm.val_func]
  have hz : (Semiterm.val e Empty.elim ∘ (Fin.elim0 : Fin 0 → TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  have hv : (Semiterm.val e Empty.elim ∘ vars n) = e := by funext i; rfl
  rw [hz,hv]
  apply modelChooseWitness good left right e
  · rw [modelApplyWitness]
    exact modelBitSentence good hBit _
  · exact modelTwoWitnessSentence good left right hEither e

end models

/-- Given Boolean-valued predicate and a provable two-way witness disjunction,
candidate PRA proves that a fixed primitive-recursive selector is a witness. -/
theorem PRA_proves_twoWitnessChoice {n : ℕ} (good : Code (n+1)) (left right : Code n)
    (hBit : PRA ⊢ bitSentence good) (hEither : PRA ⊢ twoWitnessSentence good left right) :
    PRA ⊢ selectedWitnessSentence good left right := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  apply modelSelectedSentence
  · exact models_of_provable (inferInstance : M↓[language] ⊧* PRA) hBit
  · exact models_of_provable (inferInstance : M↓[language] ⊧* PRA) hEither

end DiophantineConsistency.PRAFiniteWitnessChoice
