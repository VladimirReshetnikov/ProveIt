import DiophantineConsistency.PRAEqualityDifference
import DiophantineConsistency.PRAOpenFormulaCoverage

/-! A candidate-PRA certified primitive-recursive equality characteristic. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAEqualityCode
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAAddition PRASubAddition
  PRAEqualityDifference PRAIsZero PRABooleanOps PRAOpenFormulaCompiler PRAOpenFormulaCoverage

def swappedSub : Code 2 := .comp subCode (.cons (.proj 1) (.cons (.proj 0) (.nil 2)))
def equalityCode : Code 2 := andCode (notCode subCode) (notCode swappedSub)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelSubSelf (x : M) : Structure.func (L := language) subCode ![x,x] =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelSubAdd x (Structure.func (L := language) (Code.zero 0) Fin.elim0)
  rw [modelAddZero] at h
  exact h

theorem modelEqualityCode (x y : M) :
    IsBit (Structure.func (L := language) equalityCode ![x,y]) ∧
      (Structure.func (L := language) equalityCode ![x,y] =
        Structure.func (L := language) oneCode Fin.elim0 ↔ x = y) := by
  simp only [equalityCode, modelAndCode, modelNotCode]
  have hs : Structure.func (L := language) swappedSub ![x,y] =
      Structure.func (L := language) subCode ![y,x] := modelSwapComposition subCode x y
  rw [hs]
  obtain ⟨hb,hc⟩ := modelMulBit _ _ (modelIsZeroBit _) (modelIsZeroBit _)
  refine ⟨hb, ?_⟩
  rw [hc, modelIsZeroCharacter, modelIsZeroCharacter]
  constructor
  · rintro ⟨hxy,hyx⟩
    exact modelBothDifferencesZero x y hxy hyx
  · rintro rfl
    exact ⟨modelSubSelf x,modelSubSelf x⟩

theorem modelEqualityBitSentence : M↓[language] ⊧ eqBitSentence equalityCode := by
  simp only [models_iff, eqBitSentence, Semiformula.eval_allClosure]
  intro e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _
  simp [Semiformula.EvalAux, eqRel, applyCode, vars, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN 2)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  exact (modelEqualityCode (e 0) (e 1)).1

theorem modelEqualityCorrectSentence : M↓[language] ⊧ eqCorrectSentence equalityCode := by
  simp only [models_iff, eqCorrectSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  intro e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _
  simp [Semiformula.EvalAux, Semiformula.neg, eqRel, applyCode, vars, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN 2)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  have h := (modelEqualityCode (e 0) (e 1)).2
  tauto

end models

/-- Candidate PRA proves the equality code is always a Boolean bit. -/
theorem PRA_proves_equalityBit : PRA ⊢ eqBitSentence equalityCode := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelEqualityBitSentence

/-- Candidate PRA proves the equality code is 1 exactly when its inputs agree. -/
theorem PRA_proves_equalityCorrect : PRA ⊢ eqCorrectSentence equalityCode := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelEqualityCorrectSentence

/-- Every Foundation open semisentence has a PR characteristic whose correctness
is provable in candidate PRA. -/
theorem PRA_proves_openCharacteristic {n : ℕ} (φ : Semisentence language n) (h : φ.Open) :
    ∃ c : Code n, Primrec (eval c) ∧ PRA ⊢ characteristicSentence c φ :=
  PRAOpenFormulaCoverage.PRA_proves_openCharacteristic equalityCode
    PRA_proves_equalityBit PRA_proves_equalityCorrect φ h

end DiophantineConsistency.PRAEqualityCode
