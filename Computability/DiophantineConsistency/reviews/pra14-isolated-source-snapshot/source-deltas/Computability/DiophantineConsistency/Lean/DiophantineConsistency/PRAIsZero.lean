import DiophantineConsistency.PRANonzeroCharacter

/-! A primitive-recursive Boolean complement and its candidate-PRA meaning. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAIsZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAExhaustion PRANonzeroCharacter PRAMultiplication

def isZeroCode : Code 1 := .prec oneCode (.zero 2)

def isZeroCharacterSentence : Sentence language :=
  ∀⁰* ((Semiformula.rel Language.ORing.Rel.eq
      ![applyCode isZeroCode (fun _ => .bvar 0), applyCode oneCode Fin.elim0]) 🡘
    (Semiformula.rel Language.ORing.Rel.eq
      ![.bvar 0, applyCode (.zero 0) Fin.elim0]) : Semisentence language 1)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelIsZeroZero : Structure.func (L := language) isZeroCode
    (fun _ => Structure.func (L := language) (Code.zero 0) Fin.elim0 : Fin 1 → M) =
    Structure.func (L := language) oneCode Fin.elim0 := by
  have h := modelBase (M := M) oneCode (Code.zero 2) (Fin.elim0 : Fin 0 → M)
  simpa [isZeroCode, Matrix.fun_eq_vec_one] using h

theorem modelIsZeroSucc (x : M) : Structure.func (L := language) isZeroCode
    (fun _ => Structure.func (L := language) Code.succ (fun _ => x)) =
    Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelStep (M := M) oneCode (Code.zero 2) ![x]
  rw [modelZero] at h
  simpa [isZeroCode, Matrix.fun_eq_vec_one] using h

theorem modelIsZeroCharacter (x : M) :
    Structure.func (L := language) isZeroCode (fun _ => x) =
      Structure.func (L := language) oneCode Fin.elim0 ↔
      x = Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
  have h := modelZeroOrSuccPred x
  constructor
  · intro hb
    rcases h with hz | hs
    · exact hz
    · have hz : Structure.func (L := language) isZeroCode (fun _ => x) =
          Structure.func (L := language) (Code.zero 0) Fin.elim0 := by
        rw [←hs]
        exact modelIsZeroSucc _
      exact False.elim (modelOneNeZero (M := M) (hb.symm.trans hz))
  · intro hz
    rw [hz]
    exact modelIsZeroZero

theorem modelIsZeroCharacterSentence : M↓[language] ⊧ isZeroCharacterSentence := by
  simp only [models_iff, isZeroCharacterSentence, Semiformula.eval_allClosure, LogicalConnective.iff]
  intro e
  change Semiformula.EvalAux (inferInstance : Structure language M) Empty.elim e _
  simp [Semiformula.EvalAux, Semiformula.neg, eqRel, applyCode, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]
  have h := modelIsZeroCharacter (e 0)
  constructor
  · by_cases hv : Structure.func (L := language) isZeroCode (fun _ => e 0) =
        Structure.func (L := language) oneCode Fin.elim0
    · exact Or.inr (h.mp hv)
    · exact Or.inl hv
  · by_cases hz' : e 0 = Structure.func (L := language) (Code.zero 0) Fin.elim0
    · exact Or.inr (h.mpr hz')
    · exact Or.inl hz'

end models

/-- Candidate PRA proves its is-zero symbol is 1 exactly at zero. -/
theorem PRA_proves_isZeroCharacter : PRA ⊢ isZeroCharacterSentence := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  exact modelIsZeroCharacterSentence

end DiophantineConsistency.PRAIsZero
