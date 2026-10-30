import DiophantineConsistency.PRAFiniteWitnessList
/-! Coordinated selection among finitely many triples of PR challenge functions. -/
set_option autoImplicit false
namespace DiophantineConsistency.PRAFiniteTripleChoice
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRATermCompilation PRABooleanOps
  PRACharacteristicBit PRASelectCode PRAFiniteWitnessChoice PRANonzeroCharacter

structure Triple (n : ℕ) where
  first : Code n
  second : Code n
  third : Code n

def applyTriple {n : ℕ} (good : Code (n+3)) (t : Triple n) : Code n :=
  .comp good (.cons t.first (.cons t.second (.cons t.third (pack n (fun i => .proj i)))))

def chooseTriple {n : ℕ} (good : Code (n+3)) (left right : Triple n) : Triple n :=
  ⟨selectAmong (applyTriple good left) left.first right.first,
   selectAmong (applyTriple good left) left.second right.second,
   selectAmong (applyTriple good left) left.third right.third⟩

def chooseList {n : ℕ} (good : Code (n+3)) (fallback : Triple n) : List (Triple n) → Triple n
  | [] => fallback
  | t :: ts => chooseTriple good t (chooseList good fallback ts)

def tripleFormula {n : ℕ} (good : Code (n+3)) (t : Triple n) : Semisentence language n :=
  Semiformula.rel Language.ORing.Rel.eq
    ![applyCode (applyTriple good t) (vars n), applyCode oneCode Fin.elim0]

def listFormula {n : ℕ} (good : Code (n+3)) (fallback : Triple n) : List (Triple n) → Semisentence language n
  | [] => tripleFormula good fallback
  | t :: ts => tripleFormula good t ⋎ listFormula good fallback ts

def listSentence {n : ℕ} (good : Code (n+3)) (fallback : Triple n) (ts : List (Triple n)) : Sentence language :=
  ∀⁰* listFormula good fallback ts

def selectedSentence {n : ℕ} (good : Code (n+3)) (fallback : Triple n) (ts : List (Triple n)) : Sentence language :=
  ∀⁰* tripleFormula good (chooseList good fallback ts)

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]

theorem modelApplyTriple {n : ℕ} (good : Code (n+3)) (t : Triple n) (e : Fin n → M) :
    Structure.func (L := language) (applyTriple good t) e =
      Structure.func (L := language) good (Fin.cases (Structure.func (L := language) t.first e)
        (Fin.cases (Structure.func (L := language) t.second e)
          (Fin.cases (Structure.func (L := language) t.third e) e))) := by
  rw [applyTriple, modelComposition]
  congr 1
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  refine Fin.cases rfl (fun k => ?_) j
  refine Fin.cases rfl (fun l => ?_) k
  simp only [getCode, getCode_pack]
  exact modelProjection l e

omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem modelTripleFormula {n : ℕ} (good : Code (n+3)) (t : Triple n) (e : Fin n → M) :
    (tripleFormula good t).Eval e Empty.elim ↔
      Structure.func (L := language) (applyTriple good t) e =
        Structure.func (L := language) oneCode Fin.elim0 := by
  simp [tripleFormula, Semiformula.eval_rel, eqRel, applyCode, vars, Function.comp_def]
  have hz : (fun i : Fin 0 => Semiterm.val e Empty.elim (Fin.elim0 i : TermN n)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  rw [hz]

theorem modelChooseTriple {n : ℕ} (good : Code (n+3)) (left right : Triple n) (e : Fin n → M)
    (hBit : IsBit (Structure.func (L := language) (applyTriple good left) e))
    (hEither : Structure.func (L := language) (applyTriple good left) e =
        Structure.func (L := language) oneCode Fin.elim0 ∨
      Structure.func (L := language) (applyTriple good right) e =
        Structure.func (L := language) oneCode Fin.elim0) :
    Structure.func (L := language) (applyTriple good (chooseTriple good left right)) e =
      Structure.func (L := language) oneCode Fin.elim0 := by
  rw [modelApplyTriple]
  simp only [chooseTriple, modelSelectAmong]
  rcases hBit with hz | ho
  · simp only [hz, modelSelectZero]
    rcases hEither with hl | hr
    · exact False.elim ((modelOneNeZero (M := M)) (hl.symm.trans hz))
    · rwa [modelApplyTriple] at hr
  · simp only [ho, modelSelectOne]
    rwa [modelApplyTriple] at ho

theorem modelChooseList {n : ℕ} (good : Code (n+3)) (fallback : Triple n) (ts : List (Triple n))
    (e : Fin n → M) (hBit : M↓[language] ⊧ bitSentence good)
    (hEither : (listFormula good fallback ts).Eval e Empty.elim) :
    (tripleFormula good (chooseList good fallback ts)).Eval e Empty.elim := by
  induction ts with
  | nil => exact hEither
  | cons t ts ih =>
    have hcases : (tripleFormula good t).Eval e Empty.elim ∨ (listFormula good fallback ts).Eval e Empty.elim := by
      simpa [listFormula] using hEither
    apply (modelTripleFormula good _ e).mpr
    apply modelChooseTriple good t (chooseList good fallback ts) e
    · rw [modelApplyTriple]
      exact modelBitSentence good hBit _
    · rcases hcases with ht | ht
      · exact Or.inl ((modelTripleFormula good t e).mp ht)
      · exact Or.inr ((modelTripleFormula good _ e).mp (ih ht))

end models

theorem PRA_proves_tripleListChoice {n : ℕ} (good : Code (n+3)) (fallback : Triple n)
    (ts : List (Triple n)) (hBit : PRA ⊢ bitSentence good)
    (hEither : PRA ⊢ listSentence good fallback ts) : PRA ⊢ selectedSentence good fallback ts := by
  apply Theory.Proof.complete_on_eq_models.{0,0}
  intro M _ _ _ _
  have hb := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hBit
  have he := models_of_provable (inferInstance : M↓[language] ⊧* PRA) hEither
  simp only [models_iff, listSentence, Semiformula.eval_allClosure] at he
  simp only [models_iff, selectedSentence, Semiformula.eval_allClosure]
  intro e
  exact modelChooseList good fallback ts e hb (he e)
/-- A finite certified disjunction gives three coordinated primitive-recursive functions. -/
theorem PRA_exists_tripleListChoice {n : ℕ} (good : Code (n+3)) (fallback : Triple n)
    (ts : List (Triple n)) (hBit : PRA ⊢ bitSentence good)
    (hEither : PRA ⊢ listSentence good fallback ts) :
    ∃ t : Triple n, Primrec (eval t.first) ∧ Primrec (eval t.second) ∧
      Primrec (eval t.third) ∧ PRA ⊢ (∀⁰* tripleFormula good t) := by
  let t := chooseList good fallback ts
  exact ⟨t, eval_primrec _, eval_primrec _, eval_primrec _,
    PRA_proves_tripleListChoice good fallback ts hBit hEither⟩
end DiophantineConsistency.PRAFiniteTripleChoice
